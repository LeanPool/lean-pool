/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block012

/-! NF weak partition development: NAR4C078C001Part041. -/


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
noncomputable def nb078_split_alpha_0009 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_199), (nb078_alpha_dummy_200 f)),
        ((nb078_alpha_dummy_168), (nb078_alpha_dummy_170 f)),
        ((nb078_alpha_dummy_167), (nb078_alpha_dummy_169 f)),
        ((nb078_alpha_dummy_197), (nb078_alpha_dummy_198 f)),
        ((nb078_alpha_dummy_171), (nb078_alpha_dummy_172 f)),
        ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
        ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
        ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
        ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
        ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
        ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.classMem (Class.cv (nb078_alpha_dummy_199))
        (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_168)))))
      (Wff.classMem (Class.cv (nb078_alpha_dummy_200 f))
        (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_170 f))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
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
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_168) ≠ (nb078_alpha_dummy_201) from (by
                                unfold nb078_alpha_dummy_201;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0208) 0))))
                            (show (nb078_alpha_dummy_170 f) ≠ (nb078_alpha_dummy_202 f) from (by
                                unfold nb078_alpha_dummy_202;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0209 f) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_168) ≠ (nb078_alpha_dummy_199) from (by
                                  unfold nb078_alpha_dummy_199;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0206) 0))))
                              (show (nb078_alpha_dummy_170 f) ≠ (nb078_alpha_dummy_200 f) from
                                (by
                                  unfold nb078_alpha_dummy_200;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0207 f) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there
                        (freshVar_injective (((Class.cv (nb078_alpha_dummy_168))).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv (nb078_alpha_dummy_170 f))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078_alpha_dummy_175) ≠
        (nb078_alpha_dummy_182) from (by
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
                  (nb078_support_mem_0181 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_183), (nb078_alpha_dummy_186 f)), ((nb078_alpha_dummy_182),
        (nb078_alpha_dummy_185 f)), ((nb078_alpha_dummy_181), (nb078_alpha_dummy_184 f)),
        ((nb078_alpha_dummy_179), (nb078_alpha_dummy_180 f)), ((nb078_alpha_dummy_175),
        (nb078_alpha_dummy_177 f)), ((nb078_alpha_dummy_176), (nb078_alpha_dummy_178 f)),
        ((nb078_alpha_dummy_201), (nb078_alpha_dummy_202 f)), ((nb078_alpha_dummy_199),
        (nb078_alpha_dummy_200 f)), ((nb078_alpha_dummy_168), (nb078_alpha_dummy_170 f)),
        ((nb078_alpha_dummy_167), (nb078_alpha_dummy_169 f)), ((nb078_alpha_dummy_197),
        (nb078_alpha_dummy_198 f)), ((nb078_alpha_dummy_171), (nb078_alpha_dummy_172 f)),
        ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010),
        (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
        ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007),
        (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        ((nb078_alpha_dummy_201), (nb078_alpha_dummy_202 f)), ((nb078_alpha_dummy_199),
        (nb078_alpha_dummy_200 f)), ((nb078_alpha_dummy_168), (nb078_alpha_dummy_170 f)),
        ((nb078_alpha_dummy_167), (nb078_alpha_dummy_169 f)), ((nb078_alpha_dummy_197),
        (nb078_alpha_dummy_198 f)), ((nb078_alpha_dummy_171), (nb078_alpha_dummy_172 f)),
        ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010),
        (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
        ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007),
        (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_175))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_182) ≠ (nb078_alpha_dummy_193) from (by
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
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed
                                [((nb078_alpha_dummy_179), (nb078_alpha_dummy_180 f)),
                                  ((nb078_alpha_dummy_175), (nb078_alpha_dummy_177 f)),
                                  ((nb078_alpha_dummy_176), (nb078_alpha_dummy_178 f)),
                                  ((nb078_alpha_dummy_201), (nb078_alpha_dummy_202 f)),
                                  ((nb078_alpha_dummy_199), (nb078_alpha_dummy_200 f)),
                                  ((nb078_alpha_dummy_168), (nb078_alpha_dummy_170 f)),
                                  ((nb078_alpha_dummy_167), (nb078_alpha_dummy_169 f)),
                                  ((nb078_alpha_dummy_197), (nb078_alpha_dummy_198 f)),
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
                                (show (nb078_alpha_dummy_175) ≠ (nb078_alpha_dummy_179) from (by
                                    unfold nb078_alpha_dummy_179;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0180) 0)))) (show
                                  (nb078_alpha_dummy_177 f) ≠ (nb078_alpha_dummy_180 f) from (by
                                    unfold nb078_alpha_dummy_180;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0181 f)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
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
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed
                                [((nb078_alpha_dummy_179), (nb078_alpha_dummy_180 f)),
                                  ((nb078_alpha_dummy_175), (nb078_alpha_dummy_177 f)),
                                  ((nb078_alpha_dummy_176), (nb078_alpha_dummy_178 f)),
                                  ((nb078_alpha_dummy_201), (nb078_alpha_dummy_202 f)),
                                  ((nb078_alpha_dummy_199), (nb078_alpha_dummy_200 f)),
                                  ((nb078_alpha_dummy_168), (nb078_alpha_dummy_170 f)),
                                  ((nb078_alpha_dummy_167), (nb078_alpha_dummy_169 f)),
                                  ((nb078_alpha_dummy_197), (nb078_alpha_dummy_198 f)),
                                  ((nb078_alpha_dummy_171), (nb078_alpha_dummy_172 f)),
                                  ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
                                  ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
                                  ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
                                  ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
                                  ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
                                  ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
                                  ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
                                  ((nb078_alpha_dummy_003), x)]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.ex (TAlphaWff.conj
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
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_168) ≠ (nb078_alpha_dummy_201) from (by
                                unfold nb078_alpha_dummy_201;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0208) 0))))
                            (show (nb078_alpha_dummy_170 f) ≠ (nb078_alpha_dummy_202 f) from (by
                                unfold nb078_alpha_dummy_202;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0209 f) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_168) ≠ (nb078_alpha_dummy_199) from (by
                                  unfold nb078_alpha_dummy_199;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0206) 0))))
                              (show (nb078_alpha_dummy_170 f) ≠ (nb078_alpha_dummy_200 f) from
                                (by
                                  unfold nb078_alpha_dummy_200;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0207 f) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there
                        (freshVar_injective (((Class.cv (nb078_alpha_dummy_168))).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv (nb078_alpha_dummy_170 f))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078_alpha_dummy_175) ≠
        (nb078_alpha_dummy_182) from (by
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
                  (nb078_support_mem_0181 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_183), (nb078_alpha_dummy_186 f)), ((nb078_alpha_dummy_182),
        (nb078_alpha_dummy_185 f)), ((nb078_alpha_dummy_181), (nb078_alpha_dummy_184 f)),
        ((nb078_alpha_dummy_179), (nb078_alpha_dummy_180 f)), ((nb078_alpha_dummy_175),
        (nb078_alpha_dummy_177 f)), ((nb078_alpha_dummy_176), (nb078_alpha_dummy_178 f)),
        ((nb078_alpha_dummy_201), (nb078_alpha_dummy_202 f)), ((nb078_alpha_dummy_199),
        (nb078_alpha_dummy_200 f)), ((nb078_alpha_dummy_168), (nb078_alpha_dummy_170 f)),
        ((nb078_alpha_dummy_167), (nb078_alpha_dummy_169 f)), ((nb078_alpha_dummy_197),
        (nb078_alpha_dummy_198 f)), ((nb078_alpha_dummy_171), (nb078_alpha_dummy_172 f)),
        ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010),
        (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
        ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007),
        (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        ((nb078_alpha_dummy_201), (nb078_alpha_dummy_202 f)), ((nb078_alpha_dummy_199),
        (nb078_alpha_dummy_200 f)), ((nb078_alpha_dummy_168), (nb078_alpha_dummy_170 f)),
        ((nb078_alpha_dummy_167), (nb078_alpha_dummy_169 f)), ((nb078_alpha_dummy_197),
        (nb078_alpha_dummy_198 f)), ((nb078_alpha_dummy_171), (nb078_alpha_dummy_172 f)),
        ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010),
        (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
        ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007),
        (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_175))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_182) ≠ (nb078_alpha_dummy_193) from (by
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
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed
                                [((nb078_alpha_dummy_179), (nb078_alpha_dummy_180 f)),
                                  ((nb078_alpha_dummy_175), (nb078_alpha_dummy_177 f)),
                                  ((nb078_alpha_dummy_176), (nb078_alpha_dummy_178 f)),
                                  ((nb078_alpha_dummy_201), (nb078_alpha_dummy_202 f)),
                                  ((nb078_alpha_dummy_199), (nb078_alpha_dummy_200 f)),
                                  ((nb078_alpha_dummy_168), (nb078_alpha_dummy_170 f)),
                                  ((nb078_alpha_dummy_167), (nb078_alpha_dummy_169 f)),
                                  ((nb078_alpha_dummy_197), (nb078_alpha_dummy_198 f)),
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
                                (show (nb078_alpha_dummy_175) ≠ (nb078_alpha_dummy_179) from (by
                                    unfold nb078_alpha_dummy_179;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0180) 0)))) (show
                                  (nb078_alpha_dummy_177 f) ≠ (nb078_alpha_dummy_180 f) from (by
                                    unfold nb078_alpha_dummy_180;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0181 f)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
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
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed
                                [((nb078_alpha_dummy_179), (nb078_alpha_dummy_180 f)),
                                  ((nb078_alpha_dummy_175), (nb078_alpha_dummy_177 f)),
                                  ((nb078_alpha_dummy_176), (nb078_alpha_dummy_178 f)),
                                  ((nb078_alpha_dummy_201), (nb078_alpha_dummy_202 f)),
                                  ((nb078_alpha_dummy_199), (nb078_alpha_dummy_200 f)),
                                  ((nb078_alpha_dummy_168), (nb078_alpha_dummy_170 f)),
                                  ((nb078_alpha_dummy_167), (nb078_alpha_dummy_169 f)),
                                  ((nb078_alpha_dummy_197), (nb078_alpha_dummy_198 f)),
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

@[expose]
noncomputable def nb078_split_alpha_0010 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
        ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
        ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
        ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
        ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classEq (Class.cv (nb078_alpha_dummy_015))
          (syn_cop (Class.cv (nb078_alpha_dummy_009)) (Class.cv (nb078_alpha_dummy_010))))
        (Wff.neg (syn_wex (nb078_alpha_dummy_011) (syn_wa
              (syn_wbr (Class.cv (nb078_alpha_dummy_009))
                (syn_ccnv (Class.cv (nb078_alpha_dummy_000)))
                (Class.cv (nb078_alpha_dummy_011))) (syn_wbr (Class.cv (nb078_alpha_dummy_011))
                (Class.cv (nb078_alpha_dummy_000)) (Class.cv (nb078_alpha_dummy_010)))))))
      (Wff.imp (Wff.classEq (Class.cv (nb078_alpha_dummy_016 f))
          (syn_cop (Class.cv (nb078_alpha_dummy_012 f)) (Class.cv (nb078_alpha_dummy_013 f))))
        (Wff.neg (syn_wex (nb078_alpha_dummy_014 f) (syn_wa
              (syn_wbr (Class.cv (nb078_alpha_dummy_012 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb078_alpha_dummy_014 f)))
              (syn_wbr (Class.cv (nb078_alpha_dummy_014 f)) (Class.cv f)
                (Class.cv (nb078_alpha_dummy_013 f))))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
            (show (nb078_alpha_dummy_010) ≠ (nb078_alpha_dummy_015) from (by
                unfold nb078_alpha_dummy_015;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0002) 0))))) (Ne.symm
            (show (nb078_alpha_dummy_013 f) ≠ (nb078_alpha_dummy_016 f) from (by
                unfold nb078_alpha_dummy_016;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0003 f) 0)))))
          (TAlphaVar.there (Ne.symm (show (nb078_alpha_dummy_009) ≠ (nb078_alpha_dummy_015) from
                (by
                  unfold nb078_alpha_dummy_015;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0000) 0)))))
            (Ne.symm (show (nb078_alpha_dummy_012 f) ≠ (nb078_alpha_dummy_016 f) from (by
                  unfold nb078_alpha_dummy_016;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0001 f) 0)))))
            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0000 x y f)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_010) ≠ (nb078_alpha_dummy_018) from
                                    (by
                                      unfold nb078_alpha_dummy_018;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0032)
                                              1)))) (show
                                    (nb078_alpha_dummy_013 f) ≠ (nb078_alpha_dummy_020 f) from
                                    (by
                                      unfold nb078_alpha_dummy_020;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0034 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb078_alpha_dummy_010) ≠ (nb078_alpha_dummy_017) from (by
                                        unfold nb078_alpha_dummy_017;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0032)
                                                0)))) (show (nb078_alpha_dummy_013 f) ≠
                                        (nb078_alpha_dummy_019 f) from (by
                                        unfold nb078_alpha_dummy_019;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0034 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_010) ≠ (nb078_alpha_dummy_047) from
                                        (by
                                          unfold nb078_alpha_dummy_047;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0036)
                                                  0)))) (show (nb078_alpha_dummy_013 f) ≠
        (nb078_alpha_dummy_048 f) from (by
                                          unfold nb078_alpha_dummy_048;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0037 f) 0))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_010) ≠
        (nb078_alpha_dummy_021) from (by
          unfold nb078_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0033) 0)))) (show (nb078_alpha_dummy_013 f) ≠
        (nb078_alpha_dummy_022 f) from (by
          unfold nb078_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0035 f) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb078_alpha_dummy_009))).fv ∪
                                      ((Class.cv (nb078_alpha_dummy_010))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪
                                      ((Class.cv (nb078_alpha_dummy_013 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb078_split_alpha_0001 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_010) ≠ (nb078_alpha_dummy_018) from
                                    (by
                                      unfold nb078_alpha_dummy_018;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0032)
                                              1)))) (show
                                    (nb078_alpha_dummy_013 f) ≠ (nb078_alpha_dummy_020 f) from
                                    (by
                                      unfold nb078_alpha_dummy_020;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0034 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb078_alpha_dummy_010) ≠ (nb078_alpha_dummy_017) from (by
                                        unfold nb078_alpha_dummy_017;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0032)
                                                0)))) (show (nb078_alpha_dummy_013 f) ≠
                                        (nb078_alpha_dummy_019 f) from (by
                                        unfold nb078_alpha_dummy_019;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0034 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_010) ≠ (nb078_alpha_dummy_047) from
                                        (by
                                          unfold nb078_alpha_dummy_047;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0036)
                                                  0)))) (show (nb078_alpha_dummy_013 f) ≠
        (nb078_alpha_dummy_048 f) from (by
                                          unfold nb078_alpha_dummy_048;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0037 f) 0))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_010) ≠
        (nb078_alpha_dummy_021) from (by
          unfold nb078_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0033) 0)))) (show (nb078_alpha_dummy_013 f) ≠
        (nb078_alpha_dummy_022 f) from (by
          unfold nb078_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0035 f) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb078_alpha_dummy_009))).fv ∪
                                      ((Class.cv (nb078_alpha_dummy_010))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪
                                      ((Class.cv (nb078_alpha_dummy_013 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb078_split_alpha_0001 x y f)))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0002 x y f)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb078_alpha_dummy_011) ≠
        (nb078_alpha_dummy_054) from (by
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
                  (nb078_support_mem_0072 f) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_011) ≠ (nb078_alpha_dummy_053) from (by
          unfold nb078_alpha_dummy_053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0070) 0)))) (show (nb078_alpha_dummy_014 f) ≠
        (nb078_alpha_dummy_055 f) from (by
          unfold nb078_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0072 f) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_011) ≠ (nb078_alpha_dummy_083) from (by
          unfold nb078_alpha_dummy_083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0074) 0)))) (show (nb078_alpha_dummy_014 f) ≠
        (nb078_alpha_dummy_084 f) from (by
          unfold nb078_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0075 f) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_011) ≠ (nb078_alpha_dummy_057) from (by
          unfold nb078_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0071) 0)))) (show (nb078_alpha_dummy_014 f) ≠
        (nb078_alpha_dummy_058 f) from (by
          unfold nb078_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0073 f) 0)))) (TAlphaVar.here _ _ _)))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_009))).fv ∪ ((Class.cv (nb078_alpha_dummy_011))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪
        ((Class.cv (nb078_alpha_dummy_014 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg
                                        (TAlphaWff.conj (nb078_split_alpha_0003 x y f)
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_085), (nb078_alpha_dummy_086 f)), ((nb078_alpha_dummy_054),
        (nb078_alpha_dummy_056 f)), ((nb078_alpha_dummy_053), (nb078_alpha_dummy_055 f)),
        ((nb078_alpha_dummy_083), (nb078_alpha_dummy_084 f)), ((nb078_alpha_dummy_057),
        (nb078_alpha_dummy_058 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
        ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009),
        (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
        ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005),
        (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb078_alpha_dummy_011) ≠
        (nb078_alpha_dummy_054) from (by
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
                  (nb078_support_mem_0072 f) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_011) ≠ (nb078_alpha_dummy_053) from (by
          unfold nb078_alpha_dummy_053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0070) 0)))) (show (nb078_alpha_dummy_014 f) ≠
        (nb078_alpha_dummy_055 f) from (by
          unfold nb078_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0072 f) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_011) ≠ (nb078_alpha_dummy_083) from (by
          unfold nb078_alpha_dummy_083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0074) 0)))) (show (nb078_alpha_dummy_014 f) ≠
        (nb078_alpha_dummy_084 f) from (by
          unfold nb078_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0075 f) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_011) ≠ (nb078_alpha_dummy_057) from (by
          unfold nb078_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0071) 0)))) (show (nb078_alpha_dummy_014 f) ≠
        (nb078_alpha_dummy_058 f) from (by
          unfold nb078_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0073 f) 0)))) (TAlphaVar.here _ _ _)))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_009))).fv ∪ ((Class.cv (nb078_alpha_dummy_011))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪
        ((Class.cv (nb078_alpha_dummy_014 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg
                                        (TAlphaWff.conj (nb078_split_alpha_0003 x y f)
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_085), (nb078_alpha_dummy_086 f)), ((nb078_alpha_dummy_054),
        (nb078_alpha_dummy_056 f)), ((nb078_alpha_dummy_053), (nb078_alpha_dummy_055 f)),
        ((nb078_alpha_dummy_083), (nb078_alpha_dummy_084 f)), ((nb078_alpha_dummy_057),
        (nb078_alpha_dummy_058 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
        ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009),
        (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
        ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005),
        (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
                  (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
                            (show (nb078_alpha_dummy_090) ≠ (nb078_alpha_dummy_093) from (by
                                unfold nb078_alpha_dummy_093;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0082) 0))))) (Ne.symm
                            (show (nb078_alpha_dummy_092 f) ≠ (nb078_alpha_dummy_094 f) from (by
                                unfold nb078_alpha_dummy_094;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0083 f) 0)))))
                          (TAlphaVar.there (Ne.symm
                              (show (nb078_alpha_dummy_089) ≠ (nb078_alpha_dummy_093) from (by
                                  unfold nb078_alpha_dummy_093;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0080) 0)))))
                            (Ne.symm (show (nb078_alpha_dummy_091 f) ≠ (nb078_alpha_dummy_094 f)
                                from (by
                                  unfold nb078_alpha_dummy_094;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0081 f) 0)))))
                            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb078_split_alpha_0004 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
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
                  (nb078_support_mem_0114 f)
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
                  (nb078_support_mem_0114 f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_090) ≠ (nb078_alpha_dummy_125)
        from (by
          unfold nb078_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0116)
                  0)))) (show (nb078_alpha_dummy_092 f) ≠ (nb078_alpha_dummy_126 f) from (by
          unfold nb078_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0117
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_090) ≠ (nb078_alpha_dummy_099)
        from (by
          unfold nb078_alpha_dummy_099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0113)
                  0)))) (show (nb078_alpha_dummy_092 f) ≠ (nb078_alpha_dummy_100 f) from (by
          unfold nb078_alpha_dummy_100;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0005 x y f))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_127), (nb078_alpha_dummy_128 f)), ((nb078_alpha_dummy_096),
        (nb078_alpha_dummy_098 f)), ((nb078_alpha_dummy_095), (nb078_alpha_dummy_097 f)),
        ((nb078_alpha_dummy_125), (nb078_alpha_dummy_126 f)), ((nb078_alpha_dummy_099),
        (nb078_alpha_dummy_100 f)), ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)),
        ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093),
        (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
        ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009),
        (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
        ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005),
        (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
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
                  (nb078_support_mem_0114 f)
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
                  (nb078_support_mem_0114 f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_090) ≠ (nb078_alpha_dummy_125)
        from (by
          unfold nb078_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0116)
                  0)))) (show (nb078_alpha_dummy_092 f) ≠ (nb078_alpha_dummy_126 f) from (by
          unfold nb078_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0117
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_090) ≠ (nb078_alpha_dummy_099)
        from (by
          unfold nb078_alpha_dummy_099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0113)
                  0)))) (show (nb078_alpha_dummy_092 f) ≠ (nb078_alpha_dummy_100 f) from (by
          unfold nb078_alpha_dummy_100;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0005 x y f))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_127), (nb078_alpha_dummy_128 f)), ((nb078_alpha_dummy_096),
        (nb078_alpha_dummy_098 f)), ((nb078_alpha_dummy_095), (nb078_alpha_dummy_097 f)),
        ((nb078_alpha_dummy_125), (nb078_alpha_dummy_126 f)), ((nb078_alpha_dummy_099),
        (nb078_alpha_dummy_100 f)), ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)),
        ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093),
        (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
        ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009),
        (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
        ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005),
        (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb078_split_alpha_0006 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
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
                  (nb078_support_mem_0152 f)
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
                  (nb078_support_mem_0152 f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_089) ≠ (nb078_alpha_dummy_161)
        from (by
          unfold nb078_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0154)
                  0)))) (show (nb078_alpha_dummy_091 f) ≠ (nb078_alpha_dummy_162 f) from (by
          unfold nb078_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0155
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_089) ≠ (nb078_alpha_dummy_135)
        from (by
          unfold nb078_alpha_dummy_135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0151)
                  0)))) (show (nb078_alpha_dummy_091 f) ≠ (nb078_alpha_dummy_136 f) from (by
          unfold nb078_alpha_dummy_136;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0007 x y f))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_163), (nb078_alpha_dummy_164 f)), ((nb078_alpha_dummy_132),
        (nb078_alpha_dummy_134 f)), ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)),
        ((nb078_alpha_dummy_161), (nb078_alpha_dummy_162 f)), ((nb078_alpha_dummy_135),
        (nb078_alpha_dummy_136 f)), ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)),
        ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093),
        (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
        ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009),
        (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
        ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005),
        (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
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
                  (nb078_support_mem_0152 f)
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
                  (nb078_support_mem_0152 f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_089) ≠ (nb078_alpha_dummy_161)
        from (by
          unfold nb078_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0154)
                  0)))) (show (nb078_alpha_dummy_091 f) ≠ (nb078_alpha_dummy_162 f) from (by
          unfold nb078_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0155
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_089) ≠ (nb078_alpha_dummy_135)
        from (by
          unfold nb078_alpha_dummy_135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0151)
                  0)))) (show (nb078_alpha_dummy_091 f) ≠ (nb078_alpha_dummy_136 f) from (by
          unfold nb078_alpha_dummy_136;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0007 x y f))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_163), (nb078_alpha_dummy_164 f)), ((nb078_alpha_dummy_132),
        (nb078_alpha_dummy_134 f)), ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)),
        ((nb078_alpha_dummy_161), (nb078_alpha_dummy_162 f)), ((nb078_alpha_dummy_135),
        (nb078_alpha_dummy_136 f)), ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)),
        ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093),
        (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
        ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009),
        (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
        ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005),
        (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there
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
                                      (mem_lt_freshVar (nb078_support_mem_0171 f) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_000) ≠ (nb078_alpha_dummy_093) from (by
                                  unfold nb078_alpha_dummy_093;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0168) 0))))
                              (show f ≠ (nb078_alpha_dummy_094 f) from (by
                                  unfold nb078_alpha_dummy_094;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0169 f) 0))))
                              (TAlphaVar.there
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
                                          (mem_lt_freshVar (nb078_support_mem_0166 f)
                                            2)))) (TAlphaVar.there
                                  (show (nb078_alpha_dummy_000) ≠ (nb078_alpha_dummy_010) from
                                    (by
                                      unfold nb078_alpha_dummy_010;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0164)
                                              1)))) (show f ≠ (nb078_alpha_dummy_013 f) from (by
                                      unfold nb078_alpha_dummy_013;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0166 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb078_alpha_dummy_000) ≠ (nb078_alpha_dummy_009) from (by
                                        unfold nb078_alpha_dummy_009;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0164)
                                                0)))) (show f ≠ (nb078_alpha_dummy_012 f) from
                                      (by
                                        unfold nb078_alpha_dummy_012;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0166 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_000) ≠ (nb078_alpha_dummy_015) from
                                        (by
                                          unfold nb078_alpha_dummy_015;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0165)
                                                  0)))) (show f ≠ (nb078_alpha_dummy_016 f) from
                                        (by
                                          unfold nb078_alpha_dummy_016;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0167 f) 0))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_000) ≠
        (nb078_alpha_dummy_007) from (by
          unfold nb078_alpha_dummy_007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0162) 0)))) (show f ≠ (nb078_alpha_dummy_008 f) from (by
          unfold nb078_alpha_dummy_008;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0163 f) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_000) ≠ (nb078_alpha_dummy_005) from (by
          unfold nb078_alpha_dummy_005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0160) 0)))) (show f ≠ (nb078_alpha_dummy_006 f) from (by
          unfold nb078_alpha_dummy_006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0161 f) 0)))) (TAlphaVar.here _ _ _)))))))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0008 x y f)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb078_alpha_dummy_010) ≠
        (nb078_alpha_dummy_168) from (by
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
                  (nb078_support_mem_0202 f) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_010) ≠ (nb078_alpha_dummy_167) from (by
          unfold nb078_alpha_dummy_167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0200) 0)))) (show (nb078_alpha_dummy_013 f) ≠
        (nb078_alpha_dummy_169 f) from (by
          unfold nb078_alpha_dummy_169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0202 f) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_010) ≠ (nb078_alpha_dummy_197) from (by
          unfold nb078_alpha_dummy_197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0204) 0)))) (show (nb078_alpha_dummy_013 f) ≠
        (nb078_alpha_dummy_198 f) from (by
          unfold nb078_alpha_dummy_198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0205 f) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_010) ≠ (nb078_alpha_dummy_171) from (by
          unfold nb078_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0201) 0)))) (show (nb078_alpha_dummy_013 f) ≠
        (nb078_alpha_dummy_172 f) from (by
          unfold nb078_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0203 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv
        (nb078_alpha_dummy_000)))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪
        ((syn_ccnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_011))).fv ∪ ((Class.cv (nb078_alpha_dummy_010))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_014 f))).fv ∪
        ((Class.cv (nb078_alpha_dummy_013 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg
                                        (TAlphaWff.conj (nb078_split_alpha_0009 x y f)
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_199), (nb078_alpha_dummy_200 f)), ((nb078_alpha_dummy_168),
        (nb078_alpha_dummy_170 f)), ((nb078_alpha_dummy_167), (nb078_alpha_dummy_169 f)),
        ((nb078_alpha_dummy_197), (nb078_alpha_dummy_198 f)), ((nb078_alpha_dummy_171),
        (nb078_alpha_dummy_172 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
        ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009),
        (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
        ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005),
        (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb078_alpha_dummy_010) ≠
        (nb078_alpha_dummy_168) from (by
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
                  (nb078_support_mem_0202 f) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_010) ≠ (nb078_alpha_dummy_167) from (by
          unfold nb078_alpha_dummy_167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0200) 0)))) (show (nb078_alpha_dummy_013 f) ≠
        (nb078_alpha_dummy_169 f) from (by
          unfold nb078_alpha_dummy_169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0202 f) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_010) ≠ (nb078_alpha_dummy_197) from (by
          unfold nb078_alpha_dummy_197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0204) 0)))) (show (nb078_alpha_dummy_013 f) ≠
        (nb078_alpha_dummy_198 f) from (by
          unfold nb078_alpha_dummy_198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0205 f) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_010) ≠ (nb078_alpha_dummy_171) from (by
          unfold nb078_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0201) 0)))) (show (nb078_alpha_dummy_013 f) ≠
        (nb078_alpha_dummy_172 f) from (by
          unfold nb078_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0203 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv
        (nb078_alpha_dummy_000)))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪
        ((syn_ccnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_011))).fv ∪ ((Class.cv (nb078_alpha_dummy_010))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_014 f))).fv ∪
        ((Class.cv (nb078_alpha_dummy_013 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg
                                        (TAlphaWff.conj (nb078_split_alpha_0009 x y f)
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_199), (nb078_alpha_dummy_200 f)), ((nb078_alpha_dummy_168),
        (nb078_alpha_dummy_170 f)), ((nb078_alpha_dummy_167), (nb078_alpha_dummy_169 f)),
        ((nb078_alpha_dummy_197), (nb078_alpha_dummy_198 f)), ((nb078_alpha_dummy_171),
        (nb078_alpha_dummy_172 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
        ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009),
        (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
        ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005),
        (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there
                (show (nb078_alpha_dummy_000) ≠ (nb078_alpha_dummy_011) from (by
                    unfold nb078_alpha_dummy_011;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0164) 2))))
                (show f ≠ (nb078_alpha_dummy_014 f) from (by
                    unfold nb078_alpha_dummy_014;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0166 f) 2))))
                (TAlphaVar.there (show (nb078_alpha_dummy_000) ≠ (nb078_alpha_dummy_010) from
                    (by
                      unfold nb078_alpha_dummy_010;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0164) 1))))
                  (show f ≠ (nb078_alpha_dummy_013 f) from (by
                      unfold nb078_alpha_dummy_013;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0166 f) 1))))
                  (TAlphaVar.there (show (nb078_alpha_dummy_000) ≠ (nb078_alpha_dummy_009) from
                      (by
                        unfold nb078_alpha_dummy_009;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0164) 0))))
                    (show f ≠ (nb078_alpha_dummy_012 f) from (by
                        unfold nb078_alpha_dummy_012;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0166 f) 0)))) (TAlphaVar.there
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
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_000) ≠ (nb078_alpha_dummy_007) from (by
                            unfold nb078_alpha_dummy_007;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0162) 0))))
                        (show f ≠ (nb078_alpha_dummy_008 f) from (by
                            unfold nb078_alpha_dummy_008;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0163 f) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_000) ≠ (nb078_alpha_dummy_005) from (by
                              unfold nb078_alpha_dummy_005;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0160) 0))))
                          (show f ≠ (nb078_alpha_dummy_006 f) from (by
                              unfold nb078_alpha_dummy_006;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0161 f) 0))))
                          (TAlphaVar.here _ _ _)))))))))))))

theorem nb078_wpp_notmem_0506 : (nb078_alpha_dummy_007) ∉ ((syn_cid)).fv := by
  simpa only [nb078_alpha_dummy_007, fv_syn_cid] using (nb078_compact_fv_empty_0026)

theorem nb078_wpp_notmem_0507 (f : Var) : (nb078_alpha_dummy_008 f) ∉ ((syn_cid)).fv := by
  simpa only [nb078_alpha_dummy_008, fv_syn_cid] using (nb078_compact_fv_empty_0027 f)

theorem nb078_wpp_notmem_0508 : (nb078_alpha_dummy_005) ∉ ((syn_cid)).fv := by
  simpa only [nb078_alpha_dummy_005, fv_syn_cid] using (nb078_compact_fv_empty_0028)

theorem nb078_wpp_notmem_0509 (f : Var) : (nb078_alpha_dummy_006 f) ∉ ((syn_cid)).fv := by
  simpa only [nb078_alpha_dummy_006, fv_syn_cid] using (nb078_compact_fv_empty_0029 f)

theorem nb078_wpp_notmem_0510 : (nb078_alpha_dummy_000) ∉ ((syn_cid)).fv := by
  simpa only [nb078_alpha_dummy_000, fv_syn_cid] using (nb078_compact_fv_empty_0030)

theorem nb078_wpp_notmem_0511 (f : Var) : f ∉ ((syn_cid)).fv := by
  simpa only [fv_syn_cid] using (nb078_compact_fv_empty_0031 f)

theorem nb078_wpp_notmem_0512 : (nb078_alpha_dummy_004) ∉ ((syn_cid)).fv := by
  simpa only [nb078_alpha_dummy_004, fv_syn_cid] using (nb078_compact_fv_empty_0032)

theorem nb078_wpp_notmem_0513 (y : Var) : y ∉ ((syn_cid)).fv := by
  simpa only [fv_syn_cid] using (nb078_compact_fv_empty_0033 y)

theorem nb078_wpp_notmem_0514 : (nb078_alpha_dummy_003) ∉ ((syn_cid)).fv := by
  simpa only [nb078_alpha_dummy_003, fv_syn_cid] using (nb078_compact_fv_empty_0034)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
