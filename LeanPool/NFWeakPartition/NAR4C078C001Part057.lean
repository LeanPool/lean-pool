/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block017

/-! NF weak partition development: NAR4C078C001Part057. -/


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
noncomputable def nb078_split_alpha_0026 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_163), (nb078_alpha_dummy_164 f)),
        ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)),
        ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)),
        ((nb078_alpha_dummy_161), (nb078_alpha_dummy_162 f)),
        ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)),
        ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)),
        ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)),
        ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)),
        ((nb078_alpha_dummy_204), (nb078_alpha_dummy_206 f)),
        ((nb078_alpha_dummy_203), (nb078_alpha_dummy_205 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_163))
          (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_132))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_163)) (syn_ccompl (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_164 f))
          (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_134 f))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_164 f))
            (syn_ccompl (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
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
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_132) ≠ (nb078_alpha_dummy_165) from (by
                                  unfold nb078_alpha_dummy_165;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0158) 0))))
                              (show (nb078_alpha_dummy_134 f) ≠ (nb078_alpha_dummy_166 f) from
                                (by
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
                                          (mem_lt_freshVar (nb078_support_mem_0156) 0)))) (show
                                  (nb078_alpha_dummy_134 f) ≠ (nb078_alpha_dummy_164 f) from (by
                                    unfold nb078_alpha_dummy_164;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0157 f)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
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
        ((nb078_alpha_dummy_165), (nb078_alpha_dummy_166 f)), ((nb078_alpha_dummy_163),
        (nb078_alpha_dummy_164 f)), ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)),
        ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)), ((nb078_alpha_dummy_161),
        (nb078_alpha_dummy_162 f)), ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)),
        ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089),
        (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)),
        ((nb078_alpha_dummy_204), (nb078_alpha_dummy_206 f)), ((nb078_alpha_dummy_203),
        (nb078_alpha_dummy_205 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
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
        ((nb078_alpha_dummy_165), (nb078_alpha_dummy_166 f)), ((nb078_alpha_dummy_163),
        (nb078_alpha_dummy_164 f)), ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)),
        ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)), ((nb078_alpha_dummy_161),
        (nb078_alpha_dummy_162 f)), ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)),
        ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089),
        (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)),
        ((nb078_alpha_dummy_204), (nb078_alpha_dummy_206 f)), ((nb078_alpha_dummy_203),
        (nb078_alpha_dummy_205 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_139))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_141
        f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_146) ≠ (nb078_alpha_dummy_157) from (by
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
                                    ((nb078_alpha_dummy_165), (nb078_alpha_dummy_166 f)),
                                    ((nb078_alpha_dummy_163), (nb078_alpha_dummy_164 f)),
                                    ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)),
                                    ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)),
                                    ((nb078_alpha_dummy_161), (nb078_alpha_dummy_162 f)),
                                    ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)),
                                    ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)),
                                    ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)),
                                    ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)),
                                    ((nb078_alpha_dummy_204), (nb078_alpha_dummy_206 f)),
                                    ((nb078_alpha_dummy_203), (nb078_alpha_dummy_205 f)),
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
                                    ((nb078_alpha_dummy_165), (nb078_alpha_dummy_166 f)),
                                    ((nb078_alpha_dummy_163), (nb078_alpha_dummy_164 f)),
                                    ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)),
                                    ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)),
                                    ((nb078_alpha_dummy_161), (nb078_alpha_dummy_162 f)),
                                    ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)),
                                    ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)),
                                    ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)),
                                    ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)),
                                    ((nb078_alpha_dummy_204), (nb078_alpha_dummy_206 f)),
                                    ((nb078_alpha_dummy_203), (nb078_alpha_dummy_205 f)),
                                    ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
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
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_132) ≠ (nb078_alpha_dummy_165) from (by
                                  unfold nb078_alpha_dummy_165;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0158) 0))))
                              (show (nb078_alpha_dummy_134 f) ≠ (nb078_alpha_dummy_166 f) from
                                (by
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
                                          (mem_lt_freshVar (nb078_support_mem_0156) 0)))) (show
                                  (nb078_alpha_dummy_134 f) ≠ (nb078_alpha_dummy_164 f) from (by
                                    unfold nb078_alpha_dummy_164;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0157 f)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
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
        ((nb078_alpha_dummy_165), (nb078_alpha_dummy_166 f)), ((nb078_alpha_dummy_163),
        (nb078_alpha_dummy_164 f)), ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)),
        ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)), ((nb078_alpha_dummy_161),
        (nb078_alpha_dummy_162 f)), ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)),
        ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089),
        (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)),
        ((nb078_alpha_dummy_204), (nb078_alpha_dummy_206 f)), ((nb078_alpha_dummy_203),
        (nb078_alpha_dummy_205 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
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
        ((nb078_alpha_dummy_165), (nb078_alpha_dummy_166 f)), ((nb078_alpha_dummy_163),
        (nb078_alpha_dummy_164 f)), ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)),
        ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)), ((nb078_alpha_dummy_161),
        (nb078_alpha_dummy_162 f)), ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)),
        ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089),
        (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)),
        ((nb078_alpha_dummy_204), (nb078_alpha_dummy_206 f)), ((nb078_alpha_dummy_203),
        (nb078_alpha_dummy_205 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_139))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_141
        f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_146) ≠ (nb078_alpha_dummy_157) from (by
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
                                    ((nb078_alpha_dummy_165), (nb078_alpha_dummy_166 f)),
                                    ((nb078_alpha_dummy_163), (nb078_alpha_dummy_164 f)),
                                    ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)),
                                    ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)),
                                    ((nb078_alpha_dummy_161), (nb078_alpha_dummy_162 f)),
                                    ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)),
                                    ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)),
                                    ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)),
                                    ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)),
                                    ((nb078_alpha_dummy_204), (nb078_alpha_dummy_206 f)),
                                    ((nb078_alpha_dummy_203), (nb078_alpha_dummy_205 f)),
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
                                    ((nb078_alpha_dummy_165), (nb078_alpha_dummy_166 f)),
                                    ((nb078_alpha_dummy_163), (nb078_alpha_dummy_164 f)),
                                    ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)),
                                    ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)),
                                    ((nb078_alpha_dummy_161), (nb078_alpha_dummy_162 f)),
                                    ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)),
                                    ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)),
                                    ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)),
                                    ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)),
                                    ((nb078_alpha_dummy_204), (nb078_alpha_dummy_206 f)),
                                    ((nb078_alpha_dummy_203), (nb078_alpha_dummy_205 f)),
                                    ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_163), (nb078_alpha_dummy_164 f)),
            ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)),
            ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)),
            ((nb078_alpha_dummy_161), (nb078_alpha_dummy_162 f)),
            ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)),
            ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)),
            ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)),
            ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)),
            ((nb078_alpha_dummy_204), (nb078_alpha_dummy_206 f)),
            ((nb078_alpha_dummy_203), (nb078_alpha_dummy_205 f)),
            ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
            ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))

@[expose]
noncomputable def nb078_split_alpha_0027 (x : Var) (y : Var) (f : Var) (dv_f_y : f ≠ y) :
    TAlphaWff
      [((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (syn_wfun (Class.cv (nb078_alpha_dummy_000))) (Wff.neg
          (Wff.classEq (syn_cdm (Class.cv (nb078_alpha_dummy_000)))
            (Class.cv (nb078_alpha_dummy_004)))))
      (Wff.imp (syn_wfun (Class.cv f))
        (Wff.neg (Wff.classEq (syn_cdm (Class.cv f)) (Class.cv y)))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex
                          (TAlphaWff.ex (TAlphaWff.neg (nb078_split_alpha_0010 x y f))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_reflOn
                        [((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
                          ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
                          ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
                          ((nb078_alpha_dummy_003), x)]
                        (syn_cid) (nb078_wpp_refl_0035 x y f)))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex
                          (TAlphaWff.ex (TAlphaWff.neg (nb078_split_alpha_0010 x y f))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_reflOn
                        [((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
                          ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
                          ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
                          ((nb078_alpha_dummy_003), x)]
                        (syn_cid) (nb078_wpp_refl_0035 x y f)))))))))) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (Ne.symm
                      (show (nb078_alpha_dummy_010) ≠ (nb078_alpha_dummy_015) from (by
                          unfold nb078_alpha_dummy_015;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0002) 0))))) (Ne.symm
                      (show (nb078_alpha_dummy_013 f) ≠ (nb078_alpha_dummy_016 f) from (by
                          unfold nb078_alpha_dummy_016;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0003 f) 0)))))
                    (TAlphaVar.there (Ne.symm
                        (show (nb078_alpha_dummy_009) ≠ (nb078_alpha_dummy_015) from (by
                            unfold nb078_alpha_dummy_015;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0000) 0))))) (Ne.symm
                        (show (nb078_alpha_dummy_012 f) ≠ (nb078_alpha_dummy_016 f) from (by
                            unfold nb078_alpha_dummy_016;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0001 f) 0)))))
                      (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0011 x y f)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb078_split_alpha_0012 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                      (nb078_split_alpha_0012 x y f))))))))))))) (TAlphaWff.ex
                (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                        (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.neg (nb078_split_alpha_0013 x y f)))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_011) ≠ (nb078_alpha_dummy_054) from (by
          unfold nb078_alpha_dummy_054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0070) 1)))) (show (nb078_alpha_dummy_014 f) ≠
        (nb078_alpha_dummy_056 f) from (by
          unfold nb078_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0072 f)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_011) ≠ (nb078_alpha_dummy_053)
        from (by
          unfold nb078_alpha_dummy_053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0070)
                  0)))) (show (nb078_alpha_dummy_014 f) ≠ (nb078_alpha_dummy_055 f) from (by
          unfold nb078_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0072 f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_011) ≠ (nb078_alpha_dummy_083)
        from (by
          unfold nb078_alpha_dummy_083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0074)
                  0)))) (show (nb078_alpha_dummy_014 f) ≠ (nb078_alpha_dummy_084 f) from (by
          unfold nb078_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0075 f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_011) ≠ (nb078_alpha_dummy_057)
        from (by
          unfold nb078_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0071)
                  0)))) (show (nb078_alpha_dummy_014 f) ≠ (nb078_alpha_dummy_058 f) from (by
          unfold nb078_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0073
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_009))).fv ∪
        ((Class.cv (nb078_alpha_dummy_011))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_012 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_014 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb078_split_alpha_0014 x y f)))))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_011) ≠ (nb078_alpha_dummy_054) from (by
          unfold nb078_alpha_dummy_054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0070) 1)))) (show (nb078_alpha_dummy_014 f) ≠
        (nb078_alpha_dummy_056 f) from (by
          unfold nb078_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0072 f)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_011) ≠ (nb078_alpha_dummy_053)
        from (by
          unfold nb078_alpha_dummy_053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0070)
                  0)))) (show (nb078_alpha_dummy_014 f) ≠ (nb078_alpha_dummy_055 f) from (by
          unfold nb078_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0072 f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_011) ≠ (nb078_alpha_dummy_083)
        from (by
          unfold nb078_alpha_dummy_083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0074)
                  0)))) (show (nb078_alpha_dummy_014 f) ≠ (nb078_alpha_dummy_084 f) from (by
          unfold nb078_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0075 f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_011) ≠ (nb078_alpha_dummy_057)
        from (by
          unfold nb078_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0071)
                  0)))) (show (nb078_alpha_dummy_014 f) ≠ (nb078_alpha_dummy_058 f) from (by
          unfold nb078_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0073
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_009))).fv ∪
        ((Class.cv (nb078_alpha_dummy_011))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_012 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_014 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb078_split_alpha_0014 x y f))))))))))))))
                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
                                      (nb078_alpha_dummy_090) ≠ (nb078_alpha_dummy_093) from (by
                                        unfold nb078_alpha_dummy_093;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0082)
                                                0))))) (Ne.symm (show
                                      (nb078_alpha_dummy_092 f) ≠ (nb078_alpha_dummy_094 f) from
                                      (by
                                        unfold nb078_alpha_dummy_094;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0083 f)
                                                0))))) (TAlphaVar.there (Ne.symm (show
                                        (nb078_alpha_dummy_089) ≠ (nb078_alpha_dummy_093) from
                                        (by
                                          unfold nb078_alpha_dummy_093;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0080)
                                                  0))))) (Ne.symm (show
                                        (nb078_alpha_dummy_091 f) ≠ (nb078_alpha_dummy_094 f)
                                        from (by
                                          unfold nb078_alpha_dummy_094;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0081 f) 0)))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg
        (nb078_split_alpha_0015 x y f))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_090) ≠ (nb078_alpha_dummy_096) from (by
          unfold
            nb078_alpha_dummy_096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0112)
                  1)))) (show (nb078_alpha_dummy_092 f) ≠ (nb078_alpha_dummy_098 f) from (by
          unfold
            nb078_alpha_dummy_098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0114
                    f)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_090) ≠ (nb078_alpha_dummy_095)
        from (by
          unfold
            nb078_alpha_dummy_095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0112)
                  0)))) (show (nb078_alpha_dummy_092 f) ≠ (nb078_alpha_dummy_097 f) from (by
          unfold
            nb078_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0114
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_090) ≠ (nb078_alpha_dummy_125)
        from (by
          unfold
            nb078_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0116)
                  0)))) (show (nb078_alpha_dummy_092 f) ≠ (nb078_alpha_dummy_126 f) from (by
          unfold
            nb078_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0117
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_090) ≠ (nb078_alpha_dummy_099)
        from (by
          unfold
            nb078_alpha_dummy_099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0113)
                  0)))) (show (nb078_alpha_dummy_092 f) ≠ (nb078_alpha_dummy_100 f) from (by
          unfold
            nb078_alpha_dummy_100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0115
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_089))).fv ∪
        ((Class.cv (nb078_alpha_dummy_090))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_091 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_092 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0016 x y f))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_127), (nb078_alpha_dummy_128 f)), ((nb078_alpha_dummy_096),
        (nb078_alpha_dummy_098 f)), ((nb078_alpha_dummy_095), (nb078_alpha_dummy_097 f)),
        ((nb078_alpha_dummy_125), (nb078_alpha_dummy_126 f)), ((nb078_alpha_dummy_099),
        (nb078_alpha_dummy_100 f)), ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)),
        ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093),
        (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
        ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009),
        (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003),
        x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_090) ≠
        (nb078_alpha_dummy_096) from (by
          unfold
            nb078_alpha_dummy_096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0112)
                  1)))) (show (nb078_alpha_dummy_092 f) ≠ (nb078_alpha_dummy_098 f) from (by
          unfold
            nb078_alpha_dummy_098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0114
                    f)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_090) ≠ (nb078_alpha_dummy_095)
        from (by
          unfold
            nb078_alpha_dummy_095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0112)
                  0)))) (show (nb078_alpha_dummy_092 f) ≠ (nb078_alpha_dummy_097 f) from (by
          unfold
            nb078_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0114
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_090) ≠ (nb078_alpha_dummy_125)
        from (by
          unfold
            nb078_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0116)
                  0)))) (show (nb078_alpha_dummy_092 f) ≠ (nb078_alpha_dummy_126 f) from (by
          unfold
            nb078_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0117
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_090) ≠ (nb078_alpha_dummy_099)
        from (by
          unfold
            nb078_alpha_dummy_099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0113)
                  0)))) (show (nb078_alpha_dummy_092 f) ≠ (nb078_alpha_dummy_100 f) from (by
          unfold
            nb078_alpha_dummy_100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0115
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_089))).fv ∪
        ((Class.cv (nb078_alpha_dummy_090))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_091 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_092 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0016 x y f))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_127), (nb078_alpha_dummy_128 f)), ((nb078_alpha_dummy_096),
        (nb078_alpha_dummy_098 f)), ((nb078_alpha_dummy_095), (nb078_alpha_dummy_097 f)),
        ((nb078_alpha_dummy_125), (nb078_alpha_dummy_126 f)), ((nb078_alpha_dummy_099),
        (nb078_alpha_dummy_100 f)), ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)),
        ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093),
        (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
        ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009),
        (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003),
        x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg
        (nb078_split_alpha_0017 x y f))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_089) ≠ (nb078_alpha_dummy_132) from (by
          unfold
            nb078_alpha_dummy_132;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0150)
                  1)))) (show (nb078_alpha_dummy_091 f) ≠ (nb078_alpha_dummy_134 f) from (by
          unfold
            nb078_alpha_dummy_134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0152
                    f)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_089) ≠ (nb078_alpha_dummy_131)
        from (by
          unfold
            nb078_alpha_dummy_131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0150)
                  0)))) (show (nb078_alpha_dummy_091 f) ≠ (nb078_alpha_dummy_133 f) from (by
          unfold
            nb078_alpha_dummy_133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0152
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_089) ≠ (nb078_alpha_dummy_161)
        from (by
          unfold
            nb078_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0154)
                  0)))) (show (nb078_alpha_dummy_091 f) ≠ (nb078_alpha_dummy_162 f) from (by
          unfold
            nb078_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0155
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_089) ≠ (nb078_alpha_dummy_135)
        from (by
          unfold
            nb078_alpha_dummy_135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0151)
                  0)))) (show (nb078_alpha_dummy_091 f) ≠ (nb078_alpha_dummy_136 f) from (by
          unfold
            nb078_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0153
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_000))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_090))).fv ∪
        ((Class.cv (nb078_alpha_dummy_089))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_092 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_091 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0018 x y f))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_163), (nb078_alpha_dummy_164 f)), ((nb078_alpha_dummy_132),
        (nb078_alpha_dummy_134 f)), ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)),
        ((nb078_alpha_dummy_161), (nb078_alpha_dummy_162 f)), ((nb078_alpha_dummy_135),
        (nb078_alpha_dummy_136 f)), ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)),
        ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093),
        (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
        ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009),
        (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003),
        x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_089) ≠
        (nb078_alpha_dummy_132) from (by
          unfold
            nb078_alpha_dummy_132;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0150)
                  1)))) (show (nb078_alpha_dummy_091 f) ≠ (nb078_alpha_dummy_134 f) from (by
          unfold
            nb078_alpha_dummy_134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0152
                    f)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_089) ≠ (nb078_alpha_dummy_131)
        from (by
          unfold
            nb078_alpha_dummy_131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0150)
                  0)))) (show (nb078_alpha_dummy_091 f) ≠ (nb078_alpha_dummy_133 f) from (by
          unfold
            nb078_alpha_dummy_133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0152
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_089) ≠ (nb078_alpha_dummy_161)
        from (by
          unfold
            nb078_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0154)
                  0)))) (show (nb078_alpha_dummy_091 f) ≠ (nb078_alpha_dummy_162 f) from (by
          unfold
            nb078_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0155
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_089) ≠ (nb078_alpha_dummy_135)
        from (by
          unfold
            nb078_alpha_dummy_135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0151)
                  0)))) (show (nb078_alpha_dummy_091 f) ≠ (nb078_alpha_dummy_136 f) from (by
          unfold
            nb078_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0153
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_000))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_090))).fv ∪
        ((Class.cv (nb078_alpha_dummy_089))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_092 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_091 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0018 x y f))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_163), (nb078_alpha_dummy_164 f)), ((nb078_alpha_dummy_132),
        (nb078_alpha_dummy_134 f)), ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)),
        ((nb078_alpha_dummy_161), (nb078_alpha_dummy_162 f)), ((nb078_alpha_dummy_135),
        (nb078_alpha_dummy_136 f)), ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)),
        ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093),
        (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
        ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009),
        (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003),
        x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_000) ≠ (nb078_alpha_dummy_090) from
                                    (by
                                      unfold nb078_alpha_dummy_090;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0170)
                                              1)))) (show f ≠ (nb078_alpha_dummy_092 f) from (by
                                      unfold nb078_alpha_dummy_092;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0171 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb078_alpha_dummy_000) ≠ (nb078_alpha_dummy_089) from (by
                                        unfold nb078_alpha_dummy_089;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0170)
                                                0)))) (show f ≠ (nb078_alpha_dummy_091 f) from
                                      (by
                                        unfold nb078_alpha_dummy_091;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0171 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_000) ≠ (nb078_alpha_dummy_093) from
                                        (by
                                          unfold nb078_alpha_dummy_093;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0168)
                                                  0)))) (show f ≠ (nb078_alpha_dummy_094 f) from
                                        (by
                                          unfold nb078_alpha_dummy_094;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0169 f) 0))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_000) ≠
        (nb078_alpha_dummy_011) from (by
          unfold nb078_alpha_dummy_011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0164) 2)))) (show f ≠ (nb078_alpha_dummy_014 f) from (by
          unfold nb078_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0166 f) 2)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_000) ≠ (nb078_alpha_dummy_010) from (by
          unfold nb078_alpha_dummy_010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0164) 1)))) (show f ≠ (nb078_alpha_dummy_013 f) from (by
          unfold nb078_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0166 f) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_000) ≠ (nb078_alpha_dummy_009) from (by
          unfold nb078_alpha_dummy_009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0164) 0)))) (show f ≠ (nb078_alpha_dummy_012 f) from (by
          unfold nb078_alpha_dummy_012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0166 f) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_000) ≠ (nb078_alpha_dummy_015) from (by
          unfold nb078_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0165) 0)))) (show f ≠ (nb078_alpha_dummy_016 f) from (by
          unfold nb078_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0167 f) 0)))) (TAlphaVar.here _ _ _)))))))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.neg (nb078_split_alpha_0019 x y f)))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_010) ≠ (nb078_alpha_dummy_168) from (by
          unfold nb078_alpha_dummy_168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0200) 1)))) (show (nb078_alpha_dummy_013 f) ≠
        (nb078_alpha_dummy_170 f) from (by
          unfold nb078_alpha_dummy_170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0202 f)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_010) ≠ (nb078_alpha_dummy_167)
        from (by
          unfold nb078_alpha_dummy_167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0200)
                  0)))) (show (nb078_alpha_dummy_013 f) ≠ (nb078_alpha_dummy_169 f) from (by
          unfold nb078_alpha_dummy_169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0202 f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_010) ≠ (nb078_alpha_dummy_197)
        from (by
          unfold nb078_alpha_dummy_197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0204)
                  0)))) (show (nb078_alpha_dummy_013 f) ≠ (nb078_alpha_dummy_198 f) from (by
          unfold nb078_alpha_dummy_198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0205 f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_010) ≠ (nb078_alpha_dummy_171)
        from (by
          unfold nb078_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0201)
                  0)))) (show (nb078_alpha_dummy_013 f) ≠ (nb078_alpha_dummy_172 f) from (by
          unfold nb078_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0203
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv)
        (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_011))).fv ∪
        ((Class.cv (nb078_alpha_dummy_010))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_014 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_013 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb078_split_alpha_0020 x y f)))))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_010) ≠ (nb078_alpha_dummy_168) from (by
          unfold nb078_alpha_dummy_168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0200) 1)))) (show (nb078_alpha_dummy_013 f) ≠
        (nb078_alpha_dummy_170 f) from (by
          unfold nb078_alpha_dummy_170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0202 f)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_010) ≠ (nb078_alpha_dummy_167)
        from (by
          unfold nb078_alpha_dummy_167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0200)
                  0)))) (show (nb078_alpha_dummy_013 f) ≠ (nb078_alpha_dummy_169 f) from (by
          unfold nb078_alpha_dummy_169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0202 f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_010) ≠ (nb078_alpha_dummy_197)
        from (by
          unfold nb078_alpha_dummy_197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0204)
                  0)))) (show (nb078_alpha_dummy_013 f) ≠ (nb078_alpha_dummy_198 f) from (by
          unfold nb078_alpha_dummy_198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0205 f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_010) ≠ (nb078_alpha_dummy_171)
        from (by
          unfold nb078_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0201)
                  0)))) (show (nb078_alpha_dummy_013 f) ≠ (nb078_alpha_dummy_172 f) from (by
          unfold nb078_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0203
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv)
        (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_011))).fv ∪
        ((Class.cv (nb078_alpha_dummy_010))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_014 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_013 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb078_split_alpha_0020 x y f))))))))))))))
                    (TAlphaClass.cv (TAlphaVar.there
                        (show (nb078_alpha_dummy_000) ≠ (nb078_alpha_dummy_011) from (by
                            unfold nb078_alpha_dummy_011;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0164) 2))))
                        (show f ≠ (nb078_alpha_dummy_014 f) from (by
                            unfold nb078_alpha_dummy_014;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0166 f) 2))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_000) ≠ (nb078_alpha_dummy_010) from (by
                              unfold nb078_alpha_dummy_010;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0164) 1))))
                          (show f ≠ (nb078_alpha_dummy_013 f) from (by
                              unfold nb078_alpha_dummy_013;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0166 f) 1))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_000) ≠ (nb078_alpha_dummy_009) from (by
                                unfold nb078_alpha_dummy_009;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0164) 0))))
                            (show f ≠ (nb078_alpha_dummy_012 f) from (by
                                unfold nb078_alpha_dummy_012;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0166 f) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_000) ≠ (nb078_alpha_dummy_015) from (by
                                  unfold nb078_alpha_dummy_015;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0165) 0))))
                              (show f ≠ (nb078_alpha_dummy_016 f) from (by
                                  unfold nb078_alpha_dummy_016;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0167 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb078_alpha_dummy_204), (nb078_alpha_dummy_206 f)),
                    ((nb078_alpha_dummy_203), (nb078_alpha_dummy_205 f)),
                    ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
                    ((nb078_alpha_dummy_003), x)] (syn_cvv) (by simp only [fv_syn_cvv])))
              (TAlphaWff.classMem (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0022 x y f))))
                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq
                          (TAlphaClass.cv (TAlphaVar.there (Ne.symm
                                (show (nb078_alpha_dummy_090) ≠ (nb078_alpha_dummy_093) from (by
                                    unfold nb078_alpha_dummy_093;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0082) 0)))))
                              (Ne.symm (show
                                  (nb078_alpha_dummy_092 f) ≠ (nb078_alpha_dummy_094 f) from (by
                                    unfold nb078_alpha_dummy_094;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0083 f)
                                            0))))) (TAlphaVar.there (Ne.symm
                                  (show (nb078_alpha_dummy_089) ≠ (nb078_alpha_dummy_093) from
                                    (by
                                      unfold nb078_alpha_dummy_093;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0080)
                                              0))))) (Ne.symm (show
                                    (nb078_alpha_dummy_091 f) ≠ (nb078_alpha_dummy_094 f) from
                                    (by
                                      unfold nb078_alpha_dummy_094;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0081 f)
                                              0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg
                                      (TAlphaWff.neg (nb078_split_alpha_0023 x y f)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_090) ≠ (nb078_alpha_dummy_096) from (by
          unfold nb078_alpha_dummy_096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0112)
                  1)))) (show (nb078_alpha_dummy_092 f) ≠ (nb078_alpha_dummy_098 f) from (by
          unfold nb078_alpha_dummy_098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0114
                    f)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_090) ≠ (nb078_alpha_dummy_095)
        from (by
          unfold nb078_alpha_dummy_095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0112)
                  0)))) (show (nb078_alpha_dummy_092 f) ≠ (nb078_alpha_dummy_097 f) from (by
          unfold nb078_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0114
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_090) ≠ (nb078_alpha_dummy_125)
        from (by
          unfold
            nb078_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0116)
                  0)))) (show (nb078_alpha_dummy_092 f) ≠ (nb078_alpha_dummy_126 f) from (by
          unfold
            nb078_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0117
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_090) ≠ (nb078_alpha_dummy_099)
        from (by
          unfold
            nb078_alpha_dummy_099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0113)
                  0)))) (show (nb078_alpha_dummy_092 f) ≠ (nb078_alpha_dummy_100 f) from (by
          unfold
            nb078_alpha_dummy_100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0115
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_089))).fv ∪
        ((Class.cv (nb078_alpha_dummy_090))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_091 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_092 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb078_split_alpha_0024 x y f))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_090) ≠ (nb078_alpha_dummy_096) from (by
          unfold nb078_alpha_dummy_096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0112)
                  1)))) (show (nb078_alpha_dummy_092 f) ≠ (nb078_alpha_dummy_098 f) from (by
          unfold nb078_alpha_dummy_098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0114
                    f)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_090) ≠ (nb078_alpha_dummy_095)
        from (by
          unfold nb078_alpha_dummy_095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0112)
                  0)))) (show (nb078_alpha_dummy_092 f) ≠ (nb078_alpha_dummy_097 f) from (by
          unfold nb078_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0114
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_090) ≠ (nb078_alpha_dummy_125)
        from (by
          unfold
            nb078_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0116)
                  0)))) (show (nb078_alpha_dummy_092 f) ≠ (nb078_alpha_dummy_126 f) from (by
          unfold
            nb078_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0117
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_090) ≠ (nb078_alpha_dummy_099)
        from (by
          unfold
            nb078_alpha_dummy_099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0113)
                  0)))) (show (nb078_alpha_dummy_092 f) ≠ (nb078_alpha_dummy_100 f) from (by
          unfold
            nb078_alpha_dummy_100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0115
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_089))).fv ∪
        ((Class.cv (nb078_alpha_dummy_090))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_091 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_092 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb078_split_alpha_0024 x y f))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg
                                      (TAlphaWff.neg (nb078_split_alpha_0025 x y f)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_089) ≠ (nb078_alpha_dummy_132) from (by
          unfold nb078_alpha_dummy_132;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0150)
                  1)))) (show (nb078_alpha_dummy_091 f) ≠ (nb078_alpha_dummy_134 f) from (by
          unfold nb078_alpha_dummy_134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0152
                    f)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_089) ≠ (nb078_alpha_dummy_131)
        from (by
          unfold nb078_alpha_dummy_131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0150)
                  0)))) (show (nb078_alpha_dummy_091 f) ≠ (nb078_alpha_dummy_133 f) from (by
          unfold nb078_alpha_dummy_133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0152
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_089) ≠ (nb078_alpha_dummy_161)
        from (by
          unfold
            nb078_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0154)
                  0)))) (show (nb078_alpha_dummy_091 f) ≠ (nb078_alpha_dummy_162 f) from (by
          unfold
            nb078_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0155
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_089) ≠ (nb078_alpha_dummy_135)
        from (by
          unfold
            nb078_alpha_dummy_135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0151)
                  0)))) (show (nb078_alpha_dummy_091 f) ≠ (nb078_alpha_dummy_136 f) from (by
          unfold
            nb078_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0153
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_000))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_090))).fv ∪
        ((Class.cv (nb078_alpha_dummy_089))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_092 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_091 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb078_split_alpha_0026 x y f))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_089) ≠ (nb078_alpha_dummy_132) from (by
          unfold nb078_alpha_dummy_132;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0150)
                  1)))) (show (nb078_alpha_dummy_091 f) ≠ (nb078_alpha_dummy_134 f) from (by
          unfold nb078_alpha_dummy_134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0152
                    f)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_089) ≠ (nb078_alpha_dummy_131)
        from (by
          unfold nb078_alpha_dummy_131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0150)
                  0)))) (show (nb078_alpha_dummy_091 f) ≠ (nb078_alpha_dummy_133 f) from (by
          unfold nb078_alpha_dummy_133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0152
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_089) ≠ (nb078_alpha_dummy_161)
        from (by
          unfold
            nb078_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0154)
                  0)))) (show (nb078_alpha_dummy_091 f) ≠ (nb078_alpha_dummy_162 f) from (by
          unfold
            nb078_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0155
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_089) ≠ (nb078_alpha_dummy_135)
        from (by
          unfold
            nb078_alpha_dummy_135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0151)
                  0)))) (show (nb078_alpha_dummy_091 f) ≠ (nb078_alpha_dummy_136 f) from (by
          unfold
            nb078_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0153
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_000))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_090))).fv ∪
        ((Class.cv (nb078_alpha_dummy_089))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_092 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_091 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb078_split_alpha_0026 x y f)))))))))))))))) (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078_alpha_dummy_000) ≠ (nb078_alpha_dummy_090) from (by
                                  unfold nb078_alpha_dummy_090;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0170) 1))))
                              (show f ≠ (nb078_alpha_dummy_092 f) from (by
                                  unfold nb078_alpha_dummy_092;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0171 f) 1))))
                              (TAlphaVar.there
                                (show (nb078_alpha_dummy_000) ≠ (nb078_alpha_dummy_089) from (by
                                    unfold nb078_alpha_dummy_089;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0170) 0))))
                                (show f ≠ (nb078_alpha_dummy_091 f) from (by
                                    unfold nb078_alpha_dummy_091;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0171 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb078_alpha_dummy_000) ≠ (nb078_alpha_dummy_093) from
                                    (by
                                      unfold nb078_alpha_dummy_093;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0168)
                                              0)))) (show f ≠ (nb078_alpha_dummy_094 f) from (by
                                      unfold nb078_alpha_dummy_094;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0169 f)
                                              0)))) (TAlphaVar.there (show
                                      (nb078_alpha_dummy_000) ≠ (nb078_alpha_dummy_204) from (by
                                        unfold nb078_alpha_dummy_204;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0248)
                                                1)))) (show f ≠ (nb078_alpha_dummy_206 f) from
                                      (by
                                        unfold nb078_alpha_dummy_206;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0249 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_000) ≠ (nb078_alpha_dummy_203) from
                                        (by
                                          unfold nb078_alpha_dummy_203;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0248)
                                                  0)))) (show f ≠ (nb078_alpha_dummy_205 f) from
                                        (by
                                          unfold nb078_alpha_dummy_205;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0249 f) 0))))
                                      (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
            (Ne.symm dv_f_y) (TAlphaVar.here _ _ _))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
