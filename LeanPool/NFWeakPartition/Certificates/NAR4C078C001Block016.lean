/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block015

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part051`. -/


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
noncomputable def nb078_split_alpha_0020 (x : Var) (y : Var) (f : Var) :
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
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb078_alpha_dummy_199))
            (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_168)))))
          (Wff.classMem (Class.cv (nb078_alpha_dummy_199)) (syn_ccompl (syn_csn (syn_c0c))))))
      (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb078_alpha_dummy_200 f))
            (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_170 f)))))
          (Wff.classMem (Class.cv (nb078_alpha_dummy_200 f))
            (syn_ccompl (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
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
                              (TAlphaVar.there
                                (show (nb078_alpha_dummy_168) ≠ (nb078_alpha_dummy_201) from (by
                                    unfold nb078_alpha_dummy_201;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0208) 0)))) (show
                                  (nb078_alpha_dummy_170 f) ≠ (nb078_alpha_dummy_202 f) from (by
                                    unfold nb078_alpha_dummy_202;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0209 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb078_alpha_dummy_168) ≠ (nb078_alpha_dummy_199) from
                                    (by
                                      unfold nb078_alpha_dummy_199;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0206)
                                              0)))) (show
                                    (nb078_alpha_dummy_170 f) ≠ (nb078_alpha_dummy_200 f) from
                                    (by
                                      unfold nb078_alpha_dummy_200;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0207 f)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
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
        ((nb078_alpha_dummy_201), (nb078_alpha_dummy_202 f)), ((nb078_alpha_dummy_199),
        (nb078_alpha_dummy_200 f)), ((nb078_alpha_dummy_168), (nb078_alpha_dummy_170 f)),
        ((nb078_alpha_dummy_167), (nb078_alpha_dummy_169 f)), ((nb078_alpha_dummy_197),
        (nb078_alpha_dummy_198 f)), ((nb078_alpha_dummy_171), (nb078_alpha_dummy_172 f)),
        ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010),
        (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
        ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_000), f),
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
        ((nb078_alpha_dummy_201), (nb078_alpha_dummy_202 f)), ((nb078_alpha_dummy_199),
        (nb078_alpha_dummy_200 f)), ((nb078_alpha_dummy_168), (nb078_alpha_dummy_170 f)),
        ((nb078_alpha_dummy_167), (nb078_alpha_dummy_169 f)), ((nb078_alpha_dummy_197),
        (nb078_alpha_dummy_198 f)), ((nb078_alpha_dummy_171), (nb078_alpha_dummy_172 f)),
        ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010),
        (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
        ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_000), f),
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
                                      ((nb078_alpha_dummy_000), f),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
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
                              (TAlphaVar.there
                                (show (nb078_alpha_dummy_168) ≠ (nb078_alpha_dummy_201) from (by
                                    unfold nb078_alpha_dummy_201;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0208) 0)))) (show
                                  (nb078_alpha_dummy_170 f) ≠ (nb078_alpha_dummy_202 f) from (by
                                    unfold nb078_alpha_dummy_202;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0209 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb078_alpha_dummy_168) ≠ (nb078_alpha_dummy_199) from
                                    (by
                                      unfold nb078_alpha_dummy_199;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0206)
                                              0)))) (show
                                    (nb078_alpha_dummy_170 f) ≠ (nb078_alpha_dummy_200 f) from
                                    (by
                                      unfold nb078_alpha_dummy_200;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0207 f)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
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
        ((nb078_alpha_dummy_201), (nb078_alpha_dummy_202 f)), ((nb078_alpha_dummy_199),
        (nb078_alpha_dummy_200 f)), ((nb078_alpha_dummy_168), (nb078_alpha_dummy_170 f)),
        ((nb078_alpha_dummy_167), (nb078_alpha_dummy_169 f)), ((nb078_alpha_dummy_197),
        (nb078_alpha_dummy_198 f)), ((nb078_alpha_dummy_171), (nb078_alpha_dummy_172 f)),
        ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010),
        (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
        ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_000), f),
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
        ((nb078_alpha_dummy_201), (nb078_alpha_dummy_202 f)), ((nb078_alpha_dummy_199),
        (nb078_alpha_dummy_200 f)), ((nb078_alpha_dummy_168), (nb078_alpha_dummy_170 f)),
        ((nb078_alpha_dummy_167), (nb078_alpha_dummy_169 f)), ((nb078_alpha_dummy_197),
        (nb078_alpha_dummy_198 f)), ((nb078_alpha_dummy_171), (nb078_alpha_dummy_172 f)),
        ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010),
        (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
        ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_000), f),
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
                                      ((nb078_alpha_dummy_000), f),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
          [((nb078_alpha_dummy_199), (nb078_alpha_dummy_200 f)),
            ((nb078_alpha_dummy_168), (nb078_alpha_dummy_170 f)),
            ((nb078_alpha_dummy_167), (nb078_alpha_dummy_169 f)),
            ((nb078_alpha_dummy_197), (nb078_alpha_dummy_198 f)),
            ((nb078_alpha_dummy_171), (nb078_alpha_dummy_172 f)),
            ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
            ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
            ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
            ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
            ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
            ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part052`. -/


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
noncomputable def nb078_split_alpha_0021 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_208), (nb078_alpha_dummy_210 f)),
        ((nb078_alpha_dummy_207), (nb078_alpha_dummy_209 f)),
        ((nb078_alpha_dummy_237), (nb078_alpha_dummy_238 f)),
        ((nb078_alpha_dummy_211), (nb078_alpha_dummy_212 f)),
        ((nb078_alpha_dummy_204), (nb078_alpha_dummy_206 f)),
        ((nb078_alpha_dummy_203), (nb078_alpha_dummy_205 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_208))
          (Class.cv (nb078_alpha_dummy_203))) (Wff.neg
          (Wff.classEq (Class.cv (nb078_alpha_dummy_207))
            (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_208))) (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_210 f))
          (Class.cv (nb078_alpha_dummy_205 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f))
            (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_210 f))) (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_203) ≠ (nb078_alpha_dummy_208) from (by
              unfold nb078_alpha_dummy_208;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0238) 1))))
          (show (nb078_alpha_dummy_205 f) ≠ (nb078_alpha_dummy_210 f) from (by
              unfold nb078_alpha_dummy_210;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0240 f) 1))))
          (TAlphaVar.there (show (nb078_alpha_dummy_203) ≠ (nb078_alpha_dummy_207) from (by
                unfold nb078_alpha_dummy_207;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0238) 0))))
            (show (nb078_alpha_dummy_205 f) ≠ (nb078_alpha_dummy_209 f) from (by
                unfold nb078_alpha_dummy_209;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0240 f) 0))))
            (TAlphaVar.there (show (nb078_alpha_dummy_203) ≠ (nb078_alpha_dummy_237) from (by
                  unfold nb078_alpha_dummy_237;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0242) 0))))
              (show (nb078_alpha_dummy_205 f) ≠ (nb078_alpha_dummy_238 f) from (by
                  unfold nb078_alpha_dummy_238;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0243 f) 0))))
              (TAlphaVar.there (show (nb078_alpha_dummy_203) ≠ (nb078_alpha_dummy_211) from (by
                    unfold nb078_alpha_dummy_211;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0239) 0))))
                (show (nb078_alpha_dummy_205 f) ≠ (nb078_alpha_dummy_212 f) from (by
                    unfold nb078_alpha_dummy_212;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0241 f) 0))))
                (TAlphaVar.there (freshVar_injective
                    (((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv)
                    (by decide))
                  (freshVar_injective (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv)
                    (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb078_alpha_dummy_204))).fv ∪
                ((Class.cv (nb078_alpha_dummy_203))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb078_alpha_dummy_206 f))).fv ∪
                ((Class.cv (nb078_alpha_dummy_205 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_208) ≠ (nb078_alpha_dummy_215) from (by
                                        unfold nb078_alpha_dummy_215;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0216)
                                                0)))) (show (nb078_alpha_dummy_210 f) ≠
                                        (nb078_alpha_dummy_217 f) from (by
                                        unfold nb078_alpha_dummy_217;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0217 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_208) ≠ (nb078_alpha_dummy_216) from
                                        (by
                                          unfold nb078_alpha_dummy_216;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0216)
                                                  1)))) (show (nb078_alpha_dummy_210 f) ≠
        (nb078_alpha_dummy_218 f) from (by
                                          unfold nb078_alpha_dummy_218;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0217 f) 1))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_208) ≠
        (nb078_alpha_dummy_241) from (by
          unfold nb078_alpha_dummy_241;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0246) 0)))) (show (nb078_alpha_dummy_210 f) ≠
        (nb078_alpha_dummy_242 f) from (by
          unfold nb078_alpha_dummy_242;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0247 f) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_208) ≠ (nb078_alpha_dummy_239) from (by
          unfold nb078_alpha_dummy_239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0244) 0)))) (show (nb078_alpha_dummy_210 f) ≠
        (nb078_alpha_dummy_240 f) from (by
          unfold nb078_alpha_dummy_240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0245 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb078_alpha_dummy_208))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb078_alpha_dummy_210 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_215) ≠ (nb078_alpha_dummy_222) from (by
          unfold nb078_alpha_dummy_222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0220)
                  1)))) (show (nb078_alpha_dummy_217 f) ≠ (nb078_alpha_dummy_225 f) from (by
          unfold nb078_alpha_dummy_225;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0221
                    f)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_215) ≠ (nb078_alpha_dummy_221)
        from (by
          unfold nb078_alpha_dummy_221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0220)
                  0)))) (show (nb078_alpha_dummy_217 f) ≠ (nb078_alpha_dummy_224 f) from (by
          unfold nb078_alpha_dummy_224;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0221
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_215) ≠ (nb078_alpha_dummy_219)
        from (by
          unfold
            nb078_alpha_dummy_219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0218)
                  0)))) (show (nb078_alpha_dummy_217 f) ≠ (nb078_alpha_dummy_220 f) from (by
          unfold
            nb078_alpha_dummy_220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0219
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_223), (nb078_alpha_dummy_226 f)), ((nb078_alpha_dummy_222),
        (nb078_alpha_dummy_225 f)), ((nb078_alpha_dummy_221), (nb078_alpha_dummy_224 f)),
        ((nb078_alpha_dummy_219), (nb078_alpha_dummy_220 f)), ((nb078_alpha_dummy_215),
        (nb078_alpha_dummy_217 f)), ((nb078_alpha_dummy_216), (nb078_alpha_dummy_218 f)),
        ((nb078_alpha_dummy_241), (nb078_alpha_dummy_242 f)), ((nb078_alpha_dummy_239),
        (nb078_alpha_dummy_240 f)), ((nb078_alpha_dummy_208), (nb078_alpha_dummy_210 f)),
        ((nb078_alpha_dummy_207), (nb078_alpha_dummy_209 f)), ((nb078_alpha_dummy_237),
        (nb078_alpha_dummy_238 f)), ((nb078_alpha_dummy_211), (nb078_alpha_dummy_212 f)),
        ((nb078_alpha_dummy_204), (nb078_alpha_dummy_206 f)), ((nb078_alpha_dummy_203),
        (nb078_alpha_dummy_205 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_222) ≠ (nb078_alpha_dummy_229) from (by
          unfold
            nb078_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0224)
                  0)))) (show (nb078_alpha_dummy_225 f) ≠ (nb078_alpha_dummy_230 f) from (by
          unfold
            nb078_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0225
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_222) ≠ (nb078_alpha_dummy_227)
        from (by
          unfold
            nb078_alpha_dummy_227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0222)
                  0)))) (show (nb078_alpha_dummy_225 f) ≠ (nb078_alpha_dummy_228 f) from (by
          unfold
            nb078_alpha_dummy_228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0223
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_223) ≠
        (nb078_alpha_dummy_229) from (by
          unfold
            nb078_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0228)
                  0)))) (show (nb078_alpha_dummy_226 f) ≠ (nb078_alpha_dummy_230 f) from (by
          unfold
            nb078_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0229
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_223) ≠ (nb078_alpha_dummy_227)
        from (by
          unfold
            nb078_alpha_dummy_227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0226)
                  0)))) (show (nb078_alpha_dummy_226 f) ≠ (nb078_alpha_dummy_228 f) from (by
          unfold
            nb078_alpha_dummy_228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0227
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_222) ≠ (nb078_alpha_dummy_229) from (by
          unfold
            nb078_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0224)
                  0)))) (show (nb078_alpha_dummy_225 f) ≠ (nb078_alpha_dummy_230 f) from (by
          unfold
            nb078_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0225
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_222) ≠ (nb078_alpha_dummy_227)
        from (by
          unfold
            nb078_alpha_dummy_227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0222)
                  0)))) (show (nb078_alpha_dummy_225 f) ≠ (nb078_alpha_dummy_228 f) from (by
          unfold
            nb078_alpha_dummy_228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0223
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_223) ≠
        (nb078_alpha_dummy_229) from (by
          unfold
            nb078_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0228)
                  0)))) (show (nb078_alpha_dummy_226 f) ≠ (nb078_alpha_dummy_230 f) from (by
          unfold
            nb078_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0229
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_223) ≠ (nb078_alpha_dummy_227)
        from (by
          unfold
            nb078_alpha_dummy_227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0226)
                  0)))) (show (nb078_alpha_dummy_226 f) ≠ (nb078_alpha_dummy_228 f) from (by
          unfold
            nb078_alpha_dummy_228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0227
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_223), (nb078_alpha_dummy_226 f)), ((nb078_alpha_dummy_222),
        (nb078_alpha_dummy_225 f)), ((nb078_alpha_dummy_221), (nb078_alpha_dummy_224 f)),
        ((nb078_alpha_dummy_219), (nb078_alpha_dummy_220 f)), ((nb078_alpha_dummy_215),
        (nb078_alpha_dummy_217 f)), ((nb078_alpha_dummy_216), (nb078_alpha_dummy_218 f)),
        ((nb078_alpha_dummy_241), (nb078_alpha_dummy_242 f)), ((nb078_alpha_dummy_239),
        (nb078_alpha_dummy_240 f)), ((nb078_alpha_dummy_208), (nb078_alpha_dummy_210 f)),
        ((nb078_alpha_dummy_207), (nb078_alpha_dummy_209 f)), ((nb078_alpha_dummy_237),
        (nb078_alpha_dummy_238 f)), ((nb078_alpha_dummy_211), (nb078_alpha_dummy_212 f)),
        ((nb078_alpha_dummy_204), (nb078_alpha_dummy_206 f)), ((nb078_alpha_dummy_203),
        (nb078_alpha_dummy_205 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_215))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_217
        f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_222) ≠ (nb078_alpha_dummy_233) from (by
          unfold
            nb078_alpha_dummy_233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0232)
                  0)))) (show (nb078_alpha_dummy_225 f) ≠ (nb078_alpha_dummy_234 f) from (by
          unfold
            nb078_alpha_dummy_234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0233
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_222) ≠ (nb078_alpha_dummy_231)
        from (by
          unfold
            nb078_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0230)
                  0)))) (show (nb078_alpha_dummy_225 f) ≠ (nb078_alpha_dummy_232 f) from (by
          unfold
            nb078_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0231
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_222) ≠
        (nb078_alpha_dummy_233) from (by
          unfold
            nb078_alpha_dummy_233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0232)
                  0)))) (show (nb078_alpha_dummy_225 f) ≠ (nb078_alpha_dummy_234 f) from (by
          unfold
            nb078_alpha_dummy_234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0233
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_222) ≠ (nb078_alpha_dummy_231)
        from (by
          unfold
            nb078_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0230)
                  0)))) (show (nb078_alpha_dummy_225 f) ≠ (nb078_alpha_dummy_232 f) from (by
          unfold
            nb078_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0231
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_223) ≠ (nb078_alpha_dummy_235) from (by
          unfold
            nb078_alpha_dummy_235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0236)
                  0)))) (show (nb078_alpha_dummy_226 f) ≠ (nb078_alpha_dummy_236 f) from (by
          unfold
            nb078_alpha_dummy_236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0237
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_223) ≠ (nb078_alpha_dummy_231)
        from (by
          unfold
            nb078_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0234)
                  0)))) (show (nb078_alpha_dummy_226 f) ≠ (nb078_alpha_dummy_232 f) from (by
          unfold
            nb078_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0235
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_223) ≠
        (nb078_alpha_dummy_235) from (by
          unfold
            nb078_alpha_dummy_235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0236)
                  0)))) (show (nb078_alpha_dummy_226 f) ≠ (nb078_alpha_dummy_236 f) from (by
          unfold
            nb078_alpha_dummy_236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0237
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_223) ≠ (nb078_alpha_dummy_231)
        from (by
          unfold
            nb078_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0234)
                  0)))) (show (nb078_alpha_dummy_226 f) ≠ (nb078_alpha_dummy_232 f) from (by
          unfold
            nb078_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0235
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_215) ≠ (nb078_alpha_dummy_219)
        from (by
          unfold nb078_alpha_dummy_219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0218) 0)))) (show (nb078_alpha_dummy_217 f) ≠
        (nb078_alpha_dummy_220 f) from (by
          unfold nb078_alpha_dummy_220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_219), (nb078_alpha_dummy_220 f)),
        ((nb078_alpha_dummy_215), (nb078_alpha_dummy_217 f)), ((nb078_alpha_dummy_216),
        (nb078_alpha_dummy_218 f)), ((nb078_alpha_dummy_241), (nb078_alpha_dummy_242 f)),
        ((nb078_alpha_dummy_239), (nb078_alpha_dummy_240 f)), ((nb078_alpha_dummy_208),
        (nb078_alpha_dummy_210 f)), ((nb078_alpha_dummy_207), (nb078_alpha_dummy_209 f)),
        ((nb078_alpha_dummy_237), (nb078_alpha_dummy_238 f)), ((nb078_alpha_dummy_211),
        (nb078_alpha_dummy_212 f)), ((nb078_alpha_dummy_204), (nb078_alpha_dummy_206 f)),
        ((nb078_alpha_dummy_203), (nb078_alpha_dummy_205 f)), ((nb078_alpha_dummy_000), f),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_215) ≠ (nb078_alpha_dummy_219) from (by
          unfold nb078_alpha_dummy_219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0218) 0)))) (show (nb078_alpha_dummy_217 f) ≠
        (nb078_alpha_dummy_220 f) from (by
          unfold nb078_alpha_dummy_220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb078_alpha_dummy_215) ≠ (nb078_alpha_dummy_219) from (by
          unfold nb078_alpha_dummy_219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0218) 0)))) (show (nb078_alpha_dummy_217 f) ≠
        (nb078_alpha_dummy_220 f) from (by
          unfold nb078_alpha_dummy_220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_219), (nb078_alpha_dummy_220 f)),
        ((nb078_alpha_dummy_215), (nb078_alpha_dummy_217 f)), ((nb078_alpha_dummy_216),
        (nb078_alpha_dummy_218 f)), ((nb078_alpha_dummy_241), (nb078_alpha_dummy_242 f)),
        ((nb078_alpha_dummy_239), (nb078_alpha_dummy_240 f)), ((nb078_alpha_dummy_208),
        (nb078_alpha_dummy_210 f)), ((nb078_alpha_dummy_207), (nb078_alpha_dummy_209 f)),
        ((nb078_alpha_dummy_237), (nb078_alpha_dummy_238 f)), ((nb078_alpha_dummy_211),
        (nb078_alpha_dummy_212 f)), ((nb078_alpha_dummy_204), (nb078_alpha_dummy_206 f)),
        ((nb078_alpha_dummy_203), (nb078_alpha_dummy_205 f)), ((nb078_alpha_dummy_000), f),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_208) ≠ (nb078_alpha_dummy_215) from (by
                                        unfold nb078_alpha_dummy_215;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0216)
                                                0)))) (show (nb078_alpha_dummy_210 f) ≠
                                        (nb078_alpha_dummy_217 f) from (by
                                        unfold nb078_alpha_dummy_217;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0217 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_208) ≠ (nb078_alpha_dummy_216) from
                                        (by
                                          unfold nb078_alpha_dummy_216;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0216)
                                                  1)))) (show (nb078_alpha_dummy_210 f) ≠
        (nb078_alpha_dummy_218 f) from (by
                                          unfold nb078_alpha_dummy_218;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0217 f) 1))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_208) ≠
        (nb078_alpha_dummy_241) from (by
          unfold nb078_alpha_dummy_241;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0246) 0)))) (show (nb078_alpha_dummy_210 f) ≠
        (nb078_alpha_dummy_242 f) from (by
          unfold nb078_alpha_dummy_242;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0247 f) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_208) ≠ (nb078_alpha_dummy_239) from (by
          unfold nb078_alpha_dummy_239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0244) 0)))) (show (nb078_alpha_dummy_210 f) ≠
        (nb078_alpha_dummy_240 f) from (by
          unfold nb078_alpha_dummy_240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0245 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb078_alpha_dummy_208))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb078_alpha_dummy_210 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_215) ≠ (nb078_alpha_dummy_222) from (by
          unfold nb078_alpha_dummy_222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0220)
                  1)))) (show (nb078_alpha_dummy_217 f) ≠ (nb078_alpha_dummy_225 f) from (by
          unfold nb078_alpha_dummy_225;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0221
                    f)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_215) ≠ (nb078_alpha_dummy_221)
        from (by
          unfold nb078_alpha_dummy_221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0220)
                  0)))) (show (nb078_alpha_dummy_217 f) ≠ (nb078_alpha_dummy_224 f) from (by
          unfold nb078_alpha_dummy_224;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0221
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_215) ≠ (nb078_alpha_dummy_219)
        from (by
          unfold
            nb078_alpha_dummy_219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0218)
                  0)))) (show (nb078_alpha_dummy_217 f) ≠ (nb078_alpha_dummy_220 f) from (by
          unfold
            nb078_alpha_dummy_220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0219
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_223), (nb078_alpha_dummy_226 f)), ((nb078_alpha_dummy_222),
        (nb078_alpha_dummy_225 f)), ((nb078_alpha_dummy_221), (nb078_alpha_dummy_224 f)),
        ((nb078_alpha_dummy_219), (nb078_alpha_dummy_220 f)), ((nb078_alpha_dummy_215),
        (nb078_alpha_dummy_217 f)), ((nb078_alpha_dummy_216), (nb078_alpha_dummy_218 f)),
        ((nb078_alpha_dummy_241), (nb078_alpha_dummy_242 f)), ((nb078_alpha_dummy_239),
        (nb078_alpha_dummy_240 f)), ((nb078_alpha_dummy_208), (nb078_alpha_dummy_210 f)),
        ((nb078_alpha_dummy_207), (nb078_alpha_dummy_209 f)), ((nb078_alpha_dummy_237),
        (nb078_alpha_dummy_238 f)), ((nb078_alpha_dummy_211), (nb078_alpha_dummy_212 f)),
        ((nb078_alpha_dummy_204), (nb078_alpha_dummy_206 f)), ((nb078_alpha_dummy_203),
        (nb078_alpha_dummy_205 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_222) ≠ (nb078_alpha_dummy_229) from (by
          unfold
            nb078_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0224)
                  0)))) (show (nb078_alpha_dummy_225 f) ≠ (nb078_alpha_dummy_230 f) from (by
          unfold
            nb078_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0225
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_222) ≠ (nb078_alpha_dummy_227)
        from (by
          unfold
            nb078_alpha_dummy_227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0222)
                  0)))) (show (nb078_alpha_dummy_225 f) ≠ (nb078_alpha_dummy_228 f) from (by
          unfold
            nb078_alpha_dummy_228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0223
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_223) ≠
        (nb078_alpha_dummy_229) from (by
          unfold
            nb078_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0228)
                  0)))) (show (nb078_alpha_dummy_226 f) ≠ (nb078_alpha_dummy_230 f) from (by
          unfold
            nb078_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0229
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_223) ≠ (nb078_alpha_dummy_227)
        from (by
          unfold
            nb078_alpha_dummy_227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0226)
                  0)))) (show (nb078_alpha_dummy_226 f) ≠ (nb078_alpha_dummy_228 f) from (by
          unfold
            nb078_alpha_dummy_228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0227
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_222) ≠ (nb078_alpha_dummy_229) from (by
          unfold
            nb078_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0224)
                  0)))) (show (nb078_alpha_dummy_225 f) ≠ (nb078_alpha_dummy_230 f) from (by
          unfold
            nb078_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0225
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_222) ≠ (nb078_alpha_dummy_227)
        from (by
          unfold
            nb078_alpha_dummy_227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0222)
                  0)))) (show (nb078_alpha_dummy_225 f) ≠ (nb078_alpha_dummy_228 f) from (by
          unfold
            nb078_alpha_dummy_228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0223
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_223) ≠
        (nb078_alpha_dummy_229) from (by
          unfold
            nb078_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0228)
                  0)))) (show (nb078_alpha_dummy_226 f) ≠ (nb078_alpha_dummy_230 f) from (by
          unfold
            nb078_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0229
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_223) ≠ (nb078_alpha_dummy_227)
        from (by
          unfold
            nb078_alpha_dummy_227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0226)
                  0)))) (show (nb078_alpha_dummy_226 f) ≠ (nb078_alpha_dummy_228 f) from (by
          unfold
            nb078_alpha_dummy_228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0227
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_223), (nb078_alpha_dummy_226 f)), ((nb078_alpha_dummy_222),
        (nb078_alpha_dummy_225 f)), ((nb078_alpha_dummy_221), (nb078_alpha_dummy_224 f)),
        ((nb078_alpha_dummy_219), (nb078_alpha_dummy_220 f)), ((nb078_alpha_dummy_215),
        (nb078_alpha_dummy_217 f)), ((nb078_alpha_dummy_216), (nb078_alpha_dummy_218 f)),
        ((nb078_alpha_dummy_241), (nb078_alpha_dummy_242 f)), ((nb078_alpha_dummy_239),
        (nb078_alpha_dummy_240 f)), ((nb078_alpha_dummy_208), (nb078_alpha_dummy_210 f)),
        ((nb078_alpha_dummy_207), (nb078_alpha_dummy_209 f)), ((nb078_alpha_dummy_237),
        (nb078_alpha_dummy_238 f)), ((nb078_alpha_dummy_211), (nb078_alpha_dummy_212 f)),
        ((nb078_alpha_dummy_204), (nb078_alpha_dummy_206 f)), ((nb078_alpha_dummy_203),
        (nb078_alpha_dummy_205 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_215))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_217
        f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_222) ≠ (nb078_alpha_dummy_233) from (by
          unfold
            nb078_alpha_dummy_233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0232)
                  0)))) (show (nb078_alpha_dummy_225 f) ≠ (nb078_alpha_dummy_234 f) from (by
          unfold
            nb078_alpha_dummy_234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0233
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_222) ≠ (nb078_alpha_dummy_231)
        from (by
          unfold
            nb078_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0230)
                  0)))) (show (nb078_alpha_dummy_225 f) ≠ (nb078_alpha_dummy_232 f) from (by
          unfold
            nb078_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0231
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_222) ≠
        (nb078_alpha_dummy_233) from (by
          unfold
            nb078_alpha_dummy_233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0232)
                  0)))) (show (nb078_alpha_dummy_225 f) ≠ (nb078_alpha_dummy_234 f) from (by
          unfold
            nb078_alpha_dummy_234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0233
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_222) ≠ (nb078_alpha_dummy_231)
        from (by
          unfold
            nb078_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0230)
                  0)))) (show (nb078_alpha_dummy_225 f) ≠ (nb078_alpha_dummy_232 f) from (by
          unfold
            nb078_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0231
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_223) ≠ (nb078_alpha_dummy_235) from (by
          unfold
            nb078_alpha_dummy_235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0236)
                  0)))) (show (nb078_alpha_dummy_226 f) ≠ (nb078_alpha_dummy_236 f) from (by
          unfold
            nb078_alpha_dummy_236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0237
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_223) ≠ (nb078_alpha_dummy_231)
        from (by
          unfold
            nb078_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0234)
                  0)))) (show (nb078_alpha_dummy_226 f) ≠ (nb078_alpha_dummy_232 f) from (by
          unfold
            nb078_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0235
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_223) ≠
        (nb078_alpha_dummy_235) from (by
          unfold
            nb078_alpha_dummy_235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0236)
                  0)))) (show (nb078_alpha_dummy_226 f) ≠ (nb078_alpha_dummy_236 f) from (by
          unfold
            nb078_alpha_dummy_236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0237
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_223) ≠ (nb078_alpha_dummy_231)
        from (by
          unfold
            nb078_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0234)
                  0)))) (show (nb078_alpha_dummy_226 f) ≠ (nb078_alpha_dummy_232 f) from (by
          unfold
            nb078_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0235
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_215) ≠ (nb078_alpha_dummy_219)
        from (by
          unfold nb078_alpha_dummy_219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0218) 0)))) (show (nb078_alpha_dummy_217 f) ≠
        (nb078_alpha_dummy_220 f) from (by
          unfold nb078_alpha_dummy_220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_219), (nb078_alpha_dummy_220 f)),
        ((nb078_alpha_dummy_215), (nb078_alpha_dummy_217 f)), ((nb078_alpha_dummy_216),
        (nb078_alpha_dummy_218 f)), ((nb078_alpha_dummy_241), (nb078_alpha_dummy_242 f)),
        ((nb078_alpha_dummy_239), (nb078_alpha_dummy_240 f)), ((nb078_alpha_dummy_208),
        (nb078_alpha_dummy_210 f)), ((nb078_alpha_dummy_207), (nb078_alpha_dummy_209 f)),
        ((nb078_alpha_dummy_237), (nb078_alpha_dummy_238 f)), ((nb078_alpha_dummy_211),
        (nb078_alpha_dummy_212 f)), ((nb078_alpha_dummy_204), (nb078_alpha_dummy_206 f)),
        ((nb078_alpha_dummy_203), (nb078_alpha_dummy_205 f)), ((nb078_alpha_dummy_000), f),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_215) ≠ (nb078_alpha_dummy_219) from (by
          unfold nb078_alpha_dummy_219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0218) 0)))) (show (nb078_alpha_dummy_217 f) ≠
        (nb078_alpha_dummy_220 f) from (by
          unfold nb078_alpha_dummy_220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb078_alpha_dummy_215) ≠ (nb078_alpha_dummy_219) from (by
          unfold nb078_alpha_dummy_219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0218) 0)))) (show (nb078_alpha_dummy_217 f) ≠
        (nb078_alpha_dummy_220 f) from (by
          unfold nb078_alpha_dummy_220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_219), (nb078_alpha_dummy_220 f)),
        ((nb078_alpha_dummy_215), (nb078_alpha_dummy_217 f)), ((nb078_alpha_dummy_216),
        (nb078_alpha_dummy_218 f)), ((nb078_alpha_dummy_241), (nb078_alpha_dummy_242 f)),
        ((nb078_alpha_dummy_239), (nb078_alpha_dummy_240 f)), ((nb078_alpha_dummy_208),
        (nb078_alpha_dummy_210 f)), ((nb078_alpha_dummy_207), (nb078_alpha_dummy_209 f)),
        ((nb078_alpha_dummy_237), (nb078_alpha_dummy_238 f)), ((nb078_alpha_dummy_211),
        (nb078_alpha_dummy_212 f)), ((nb078_alpha_dummy_204), (nb078_alpha_dummy_206 f)),
        ((nb078_alpha_dummy_203), (nb078_alpha_dummy_205 f)), ((nb078_alpha_dummy_000), f),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb078_alpha_dummy_239), (nb078_alpha_dummy_240 f)),
                    ((nb078_alpha_dummy_208), (nb078_alpha_dummy_210 f)),
                    ((nb078_alpha_dummy_207), (nb078_alpha_dummy_209 f)),
                    ((nb078_alpha_dummy_237), (nb078_alpha_dummy_238 f)),
                    ((nb078_alpha_dummy_211), (nb078_alpha_dummy_212 f)),
                    ((nb078_alpha_dummy_204), (nb078_alpha_dummy_206 f)),
                    ((nb078_alpha_dummy_203), (nb078_alpha_dummy_205 f)),
                    ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
                    ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part053`. -/


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
noncomputable def nb078_split_alpha_0022 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_211), (nb078_alpha_dummy_212 f)),
        ((nb078_alpha_dummy_204), (nb078_alpha_dummy_206 f)),
        ((nb078_alpha_dummy_203), (nb078_alpha_dummy_205 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_211)) (syn_ccompl
            (Class.cab (nb078_alpha_dummy_207)
              (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_204))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_207))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_208)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_211)) (syn_ccompl
              (Class.cab (nb078_alpha_dummy_207)
                (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_203))
                  (Wff.classEq (Class.cv (nb078_alpha_dummy_207))
                    (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_208)))
                      (syn_csn (syn_c0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_212 f)) (syn_ccompl
            (Class.cab (nb078_alpha_dummy_209 f)
              (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_206 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_210 f)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_212 f)) (syn_ccompl
              (Class.cab (nb078_alpha_dummy_209 f)
                (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_205 f))
                  (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f))
                    (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_210 f)))
                      (syn_csn (syn_c0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_204) ≠ (nb078_alpha_dummy_208) from (by
                              unfold nb078_alpha_dummy_208;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0210) 1))))
                          (show (nb078_alpha_dummy_206 f) ≠ (nb078_alpha_dummy_210 f) from (by
                              unfold nb078_alpha_dummy_210;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0212 f) 1))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_204) ≠ (nb078_alpha_dummy_207) from (by
                                unfold nb078_alpha_dummy_207;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0210) 0))))
                            (show (nb078_alpha_dummy_206 f) ≠ (nb078_alpha_dummy_209 f) from (by
                                unfold nb078_alpha_dummy_209;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0212 f) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_204) ≠ (nb078_alpha_dummy_213) from (by
                                  unfold nb078_alpha_dummy_213;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0214) 0))))
                              (show (nb078_alpha_dummy_206 f) ≠ (nb078_alpha_dummy_214 f) from
                                (by
                                  unfold nb078_alpha_dummy_214;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0215 f) 0))))
                              (TAlphaVar.there
                                (show (nb078_alpha_dummy_204) ≠ (nb078_alpha_dummy_211) from (by
                                    unfold nb078_alpha_dummy_211;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0211) 0)))) (show
                                  (nb078_alpha_dummy_206 f) ≠ (nb078_alpha_dummy_212 f) from (by
                                    unfold nb078_alpha_dummy_212;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0213 f)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb078_alpha_dummy_204))).fv ∪
                              ((Class.cv (nb078_alpha_dummy_203))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_206 f))).fv ∪
                              ((Class.cv (nb078_alpha_dummy_205 f))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_208) ≠ (nb078_alpha_dummy_215) from
                                    (by
                                      unfold nb078_alpha_dummy_215;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0216)
                                              0)))) (show
                                    (nb078_alpha_dummy_210 f) ≠ (nb078_alpha_dummy_217 f) from
                                    (by
                                      unfold nb078_alpha_dummy_217;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0217 f)
                                              0)))) (TAlphaVar.there (show
                                      (nb078_alpha_dummy_208) ≠ (nb078_alpha_dummy_216) from (by
                                        unfold nb078_alpha_dummy_216;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0216)
                                                1)))) (show (nb078_alpha_dummy_210 f) ≠
                                        (nb078_alpha_dummy_218 f) from (by
                                        unfold nb078_alpha_dummy_218;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0217 f)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb078_alpha_dummy_208))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb078_alpha_dummy_210 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_215) ≠ (nb078_alpha_dummy_222) from (by
          unfold nb078_alpha_dummy_222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0220)
                  1)))) (show (nb078_alpha_dummy_217 f) ≠ (nb078_alpha_dummy_225 f) from (by
          unfold nb078_alpha_dummy_225;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0221 f)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_215) ≠ (nb078_alpha_dummy_221)
        from (by
          unfold nb078_alpha_dummy_221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0220)
                  0)))) (show (nb078_alpha_dummy_217 f) ≠ (nb078_alpha_dummy_224 f) from (by
          unfold nb078_alpha_dummy_224;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0221
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_215) ≠ (nb078_alpha_dummy_219)
        from (by
          unfold nb078_alpha_dummy_219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0218)
                  0)))) (show (nb078_alpha_dummy_217 f) ≠ (nb078_alpha_dummy_220 f) from (by
          unfold nb078_alpha_dummy_220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0219
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_223), (nb078_alpha_dummy_226 f)), ((nb078_alpha_dummy_222),
        (nb078_alpha_dummy_225 f)), ((nb078_alpha_dummy_221), (nb078_alpha_dummy_224 f)),
        ((nb078_alpha_dummy_219), (nb078_alpha_dummy_220 f)), ((nb078_alpha_dummy_215),
        (nb078_alpha_dummy_217 f)), ((nb078_alpha_dummy_216), (nb078_alpha_dummy_218 f)),
        ((nb078_alpha_dummy_208), (nb078_alpha_dummy_210 f)), ((nb078_alpha_dummy_207),
        (nb078_alpha_dummy_209 f)), ((nb078_alpha_dummy_213), (nb078_alpha_dummy_214 f)),
        ((nb078_alpha_dummy_211), (nb078_alpha_dummy_212 f)), ((nb078_alpha_dummy_204),
        (nb078_alpha_dummy_206 f)), ((nb078_alpha_dummy_203), (nb078_alpha_dummy_205 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_222) ≠ (nb078_alpha_dummy_229) from (by
          unfold
            nb078_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0224)
                  0)))) (show (nb078_alpha_dummy_225 f) ≠ (nb078_alpha_dummy_230 f) from (by
          unfold
            nb078_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0225
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_222) ≠ (nb078_alpha_dummy_227)
        from (by
          unfold
            nb078_alpha_dummy_227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0222)
                  0)))) (show (nb078_alpha_dummy_225 f) ≠ (nb078_alpha_dummy_228 f) from (by
          unfold
            nb078_alpha_dummy_228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0223
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_223) ≠
        (nb078_alpha_dummy_229) from (by
          unfold
            nb078_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0228)
                  0)))) (show (nb078_alpha_dummy_226 f) ≠ (nb078_alpha_dummy_230 f) from (by
          unfold
            nb078_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0229
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_223) ≠ (nb078_alpha_dummy_227)
        from (by
          unfold
            nb078_alpha_dummy_227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0226)
                  0)))) (show (nb078_alpha_dummy_226 f) ≠ (nb078_alpha_dummy_228 f) from (by
          unfold
            nb078_alpha_dummy_228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0227
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_222) ≠ (nb078_alpha_dummy_229) from (by
          unfold
            nb078_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0224)
                  0)))) (show (nb078_alpha_dummy_225 f) ≠ (nb078_alpha_dummy_230 f) from (by
          unfold
            nb078_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0225
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_222) ≠ (nb078_alpha_dummy_227)
        from (by
          unfold
            nb078_alpha_dummy_227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0222)
                  0)))) (show (nb078_alpha_dummy_225 f) ≠ (nb078_alpha_dummy_228 f) from (by
          unfold
            nb078_alpha_dummy_228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0223
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_223) ≠
        (nb078_alpha_dummy_229) from (by
          unfold
            nb078_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0228)
                  0)))) (show (nb078_alpha_dummy_226 f) ≠ (nb078_alpha_dummy_230 f) from (by
          unfold
            nb078_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0229
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_223) ≠ (nb078_alpha_dummy_227)
        from (by
          unfold
            nb078_alpha_dummy_227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0226)
                  0)))) (show (nb078_alpha_dummy_226 f) ≠ (nb078_alpha_dummy_228 f) from (by
          unfold
            nb078_alpha_dummy_228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0227
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_223), (nb078_alpha_dummy_226 f)), ((nb078_alpha_dummy_222),
        (nb078_alpha_dummy_225 f)), ((nb078_alpha_dummy_221), (nb078_alpha_dummy_224 f)),
        ((nb078_alpha_dummy_219), (nb078_alpha_dummy_220 f)), ((nb078_alpha_dummy_215),
        (nb078_alpha_dummy_217 f)), ((nb078_alpha_dummy_216), (nb078_alpha_dummy_218 f)),
        ((nb078_alpha_dummy_208), (nb078_alpha_dummy_210 f)), ((nb078_alpha_dummy_207),
        (nb078_alpha_dummy_209 f)), ((nb078_alpha_dummy_213), (nb078_alpha_dummy_214 f)),
        ((nb078_alpha_dummy_211), (nb078_alpha_dummy_212 f)), ((nb078_alpha_dummy_204),
        (nb078_alpha_dummy_206 f)), ((nb078_alpha_dummy_203), (nb078_alpha_dummy_205 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_215))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_217
        f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_222) ≠ (nb078_alpha_dummy_233) from (by
          unfold
            nb078_alpha_dummy_233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0232)
                  0)))) (show (nb078_alpha_dummy_225 f) ≠ (nb078_alpha_dummy_234 f) from (by
          unfold
            nb078_alpha_dummy_234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0233
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_222) ≠ (nb078_alpha_dummy_231)
        from (by
          unfold
            nb078_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0230)
                  0)))) (show (nb078_alpha_dummy_225 f) ≠ (nb078_alpha_dummy_232 f) from (by
          unfold
            nb078_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0231
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_222) ≠
        (nb078_alpha_dummy_233) from (by
          unfold
            nb078_alpha_dummy_233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0232)
                  0)))) (show (nb078_alpha_dummy_225 f) ≠ (nb078_alpha_dummy_234 f) from (by
          unfold
            nb078_alpha_dummy_234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0233
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_222) ≠ (nb078_alpha_dummy_231)
        from (by
          unfold
            nb078_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0230)
                  0)))) (show (nb078_alpha_dummy_225 f) ≠ (nb078_alpha_dummy_232 f) from (by
          unfold
            nb078_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0231
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_223) ≠ (nb078_alpha_dummy_235) from (by
          unfold
            nb078_alpha_dummy_235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0236)
                  0)))) (show (nb078_alpha_dummy_226 f) ≠ (nb078_alpha_dummy_236 f) from (by
          unfold
            nb078_alpha_dummy_236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0237
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_223) ≠ (nb078_alpha_dummy_231)
        from (by
          unfold
            nb078_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0234)
                  0)))) (show (nb078_alpha_dummy_226 f) ≠ (nb078_alpha_dummy_232 f) from (by
          unfold
            nb078_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0235
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_223) ≠
        (nb078_alpha_dummy_235) from (by
          unfold
            nb078_alpha_dummy_235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0236)
                  0)))) (show (nb078_alpha_dummy_226 f) ≠ (nb078_alpha_dummy_236 f) from (by
          unfold
            nb078_alpha_dummy_236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0237
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_223) ≠ (nb078_alpha_dummy_231)
        from (by
          unfold
            nb078_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0234)
                  0)))) (show (nb078_alpha_dummy_226 f) ≠ (nb078_alpha_dummy_232 f) from (by
          unfold
            nb078_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0235
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_215) ≠ (nb078_alpha_dummy_219) from (by
          unfold nb078_alpha_dummy_219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0218) 0)))) (show (nb078_alpha_dummy_217 f) ≠
        (nb078_alpha_dummy_220 f) from (by
          unfold nb078_alpha_dummy_220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_219),
        (nb078_alpha_dummy_220 f)), ((nb078_alpha_dummy_215), (nb078_alpha_dummy_217 f)),
        ((nb078_alpha_dummy_216), (nb078_alpha_dummy_218 f)), ((nb078_alpha_dummy_208),
        (nb078_alpha_dummy_210 f)), ((nb078_alpha_dummy_207), (nb078_alpha_dummy_209 f)),
        ((nb078_alpha_dummy_213), (nb078_alpha_dummy_214 f)), ((nb078_alpha_dummy_211),
        (nb078_alpha_dummy_212 f)), ((nb078_alpha_dummy_204), (nb078_alpha_dummy_206 f)),
        ((nb078_alpha_dummy_203), (nb078_alpha_dummy_205 f)), ((nb078_alpha_dummy_000), f),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078_alpha_dummy_215) ≠
        (nb078_alpha_dummy_219) from (by
          unfold nb078_alpha_dummy_219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0218) 0)))) (show (nb078_alpha_dummy_217 f) ≠
        (nb078_alpha_dummy_220 f) from (by
          unfold nb078_alpha_dummy_220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_215) ≠ (nb078_alpha_dummy_219) from (by
          unfold nb078_alpha_dummy_219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0218) 0)))) (show (nb078_alpha_dummy_217 f) ≠
        (nb078_alpha_dummy_220 f) from (by
          unfold nb078_alpha_dummy_220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_219),
        (nb078_alpha_dummy_220 f)), ((nb078_alpha_dummy_215), (nb078_alpha_dummy_217 f)),
        ((nb078_alpha_dummy_216), (nb078_alpha_dummy_218 f)), ((nb078_alpha_dummy_208),
        (nb078_alpha_dummy_210 f)), ((nb078_alpha_dummy_207), (nb078_alpha_dummy_209 f)),
        ((nb078_alpha_dummy_213), (nb078_alpha_dummy_214 f)), ((nb078_alpha_dummy_211),
        (nb078_alpha_dummy_212 f)), ((nb078_alpha_dummy_204), (nb078_alpha_dummy_206 f)),
        ((nb078_alpha_dummy_203), (nb078_alpha_dummy_205 f)), ((nb078_alpha_dummy_000), f),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_204) ≠ (nb078_alpha_dummy_208) from (by
                              unfold nb078_alpha_dummy_208;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0210) 1))))
                          (show (nb078_alpha_dummy_206 f) ≠ (nb078_alpha_dummy_210 f) from (by
                              unfold nb078_alpha_dummy_210;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0212 f) 1))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_204) ≠ (nb078_alpha_dummy_207) from (by
                                unfold nb078_alpha_dummy_207;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0210) 0))))
                            (show (nb078_alpha_dummy_206 f) ≠ (nb078_alpha_dummy_209 f) from (by
                                unfold nb078_alpha_dummy_209;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0212 f) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_204) ≠ (nb078_alpha_dummy_213) from (by
                                  unfold nb078_alpha_dummy_213;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0214) 0))))
                              (show (nb078_alpha_dummy_206 f) ≠ (nb078_alpha_dummy_214 f) from
                                (by
                                  unfold nb078_alpha_dummy_214;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0215 f) 0))))
                              (TAlphaVar.there
                                (show (nb078_alpha_dummy_204) ≠ (nb078_alpha_dummy_211) from (by
                                    unfold nb078_alpha_dummy_211;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0211) 0)))) (show
                                  (nb078_alpha_dummy_206 f) ≠ (nb078_alpha_dummy_212 f) from (by
                                    unfold nb078_alpha_dummy_212;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0213 f)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb078_alpha_dummy_204))).fv ∪
                              ((Class.cv (nb078_alpha_dummy_203))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_206 f))).fv ∪
                              ((Class.cv (nb078_alpha_dummy_205 f))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_208) ≠ (nb078_alpha_dummy_215) from
                                    (by
                                      unfold nb078_alpha_dummy_215;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0216)
                                              0)))) (show
                                    (nb078_alpha_dummy_210 f) ≠ (nb078_alpha_dummy_217 f) from
                                    (by
                                      unfold nb078_alpha_dummy_217;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0217 f)
                                              0)))) (TAlphaVar.there (show
                                      (nb078_alpha_dummy_208) ≠ (nb078_alpha_dummy_216) from (by
                                        unfold nb078_alpha_dummy_216;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0216)
                                                1)))) (show (nb078_alpha_dummy_210 f) ≠
                                        (nb078_alpha_dummy_218 f) from (by
                                        unfold nb078_alpha_dummy_218;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0217 f)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb078_alpha_dummy_208))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb078_alpha_dummy_210 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_215) ≠ (nb078_alpha_dummy_222) from (by
          unfold nb078_alpha_dummy_222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0220)
                  1)))) (show (nb078_alpha_dummy_217 f) ≠ (nb078_alpha_dummy_225 f) from (by
          unfold nb078_alpha_dummy_225;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0221 f)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_215) ≠ (nb078_alpha_dummy_221)
        from (by
          unfold nb078_alpha_dummy_221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0220)
                  0)))) (show (nb078_alpha_dummy_217 f) ≠ (nb078_alpha_dummy_224 f) from (by
          unfold nb078_alpha_dummy_224;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0221
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_215) ≠ (nb078_alpha_dummy_219)
        from (by
          unfold nb078_alpha_dummy_219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0218)
                  0)))) (show (nb078_alpha_dummy_217 f) ≠ (nb078_alpha_dummy_220 f) from (by
          unfold nb078_alpha_dummy_220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0219
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_223), (nb078_alpha_dummy_226 f)), ((nb078_alpha_dummy_222),
        (nb078_alpha_dummy_225 f)), ((nb078_alpha_dummy_221), (nb078_alpha_dummy_224 f)),
        ((nb078_alpha_dummy_219), (nb078_alpha_dummy_220 f)), ((nb078_alpha_dummy_215),
        (nb078_alpha_dummy_217 f)), ((nb078_alpha_dummy_216), (nb078_alpha_dummy_218 f)),
        ((nb078_alpha_dummy_208), (nb078_alpha_dummy_210 f)), ((nb078_alpha_dummy_207),
        (nb078_alpha_dummy_209 f)), ((nb078_alpha_dummy_213), (nb078_alpha_dummy_214 f)),
        ((nb078_alpha_dummy_211), (nb078_alpha_dummy_212 f)), ((nb078_alpha_dummy_204),
        (nb078_alpha_dummy_206 f)), ((nb078_alpha_dummy_203), (nb078_alpha_dummy_205 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_222) ≠ (nb078_alpha_dummy_229) from (by
          unfold
            nb078_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0224)
                  0)))) (show (nb078_alpha_dummy_225 f) ≠ (nb078_alpha_dummy_230 f) from (by
          unfold
            nb078_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0225
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_222) ≠ (nb078_alpha_dummy_227)
        from (by
          unfold
            nb078_alpha_dummy_227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0222)
                  0)))) (show (nb078_alpha_dummy_225 f) ≠ (nb078_alpha_dummy_228 f) from (by
          unfold
            nb078_alpha_dummy_228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0223
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_223) ≠
        (nb078_alpha_dummy_229) from (by
          unfold
            nb078_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0228)
                  0)))) (show (nb078_alpha_dummy_226 f) ≠ (nb078_alpha_dummy_230 f) from (by
          unfold
            nb078_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0229
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_223) ≠ (nb078_alpha_dummy_227)
        from (by
          unfold
            nb078_alpha_dummy_227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0226)
                  0)))) (show (nb078_alpha_dummy_226 f) ≠ (nb078_alpha_dummy_228 f) from (by
          unfold
            nb078_alpha_dummy_228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0227
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_222) ≠ (nb078_alpha_dummy_229) from (by
          unfold
            nb078_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0224)
                  0)))) (show (nb078_alpha_dummy_225 f) ≠ (nb078_alpha_dummy_230 f) from (by
          unfold
            nb078_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0225
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_222) ≠ (nb078_alpha_dummy_227)
        from (by
          unfold
            nb078_alpha_dummy_227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0222)
                  0)))) (show (nb078_alpha_dummy_225 f) ≠ (nb078_alpha_dummy_228 f) from (by
          unfold
            nb078_alpha_dummy_228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0223
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_223) ≠
        (nb078_alpha_dummy_229) from (by
          unfold
            nb078_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0228)
                  0)))) (show (nb078_alpha_dummy_226 f) ≠ (nb078_alpha_dummy_230 f) from (by
          unfold
            nb078_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0229
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_223) ≠ (nb078_alpha_dummy_227)
        from (by
          unfold
            nb078_alpha_dummy_227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0226)
                  0)))) (show (nb078_alpha_dummy_226 f) ≠ (nb078_alpha_dummy_228 f) from (by
          unfold
            nb078_alpha_dummy_228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0227
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_223), (nb078_alpha_dummy_226 f)), ((nb078_alpha_dummy_222),
        (nb078_alpha_dummy_225 f)), ((nb078_alpha_dummy_221), (nb078_alpha_dummy_224 f)),
        ((nb078_alpha_dummy_219), (nb078_alpha_dummy_220 f)), ((nb078_alpha_dummy_215),
        (nb078_alpha_dummy_217 f)), ((nb078_alpha_dummy_216), (nb078_alpha_dummy_218 f)),
        ((nb078_alpha_dummy_208), (nb078_alpha_dummy_210 f)), ((nb078_alpha_dummy_207),
        (nb078_alpha_dummy_209 f)), ((nb078_alpha_dummy_213), (nb078_alpha_dummy_214 f)),
        ((nb078_alpha_dummy_211), (nb078_alpha_dummy_212 f)), ((nb078_alpha_dummy_204),
        (nb078_alpha_dummy_206 f)), ((nb078_alpha_dummy_203), (nb078_alpha_dummy_205 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_215))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_217
        f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_222) ≠ (nb078_alpha_dummy_233) from (by
          unfold
            nb078_alpha_dummy_233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0232)
                  0)))) (show (nb078_alpha_dummy_225 f) ≠ (nb078_alpha_dummy_234 f) from (by
          unfold
            nb078_alpha_dummy_234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0233
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_222) ≠ (nb078_alpha_dummy_231)
        from (by
          unfold
            nb078_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0230)
                  0)))) (show (nb078_alpha_dummy_225 f) ≠ (nb078_alpha_dummy_232 f) from (by
          unfold
            nb078_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0231
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_222) ≠
        (nb078_alpha_dummy_233) from (by
          unfold
            nb078_alpha_dummy_233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0232)
                  0)))) (show (nb078_alpha_dummy_225 f) ≠ (nb078_alpha_dummy_234 f) from (by
          unfold
            nb078_alpha_dummy_234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0233
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_222) ≠ (nb078_alpha_dummy_231)
        from (by
          unfold
            nb078_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0230)
                  0)))) (show (nb078_alpha_dummy_225 f) ≠ (nb078_alpha_dummy_232 f) from (by
          unfold
            nb078_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0231
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_223) ≠ (nb078_alpha_dummy_235) from (by
          unfold
            nb078_alpha_dummy_235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0236)
                  0)))) (show (nb078_alpha_dummy_226 f) ≠ (nb078_alpha_dummy_236 f) from (by
          unfold
            nb078_alpha_dummy_236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0237
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_223) ≠ (nb078_alpha_dummy_231)
        from (by
          unfold
            nb078_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0234)
                  0)))) (show (nb078_alpha_dummy_226 f) ≠ (nb078_alpha_dummy_232 f) from (by
          unfold
            nb078_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0235
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_223) ≠
        (nb078_alpha_dummy_235) from (by
          unfold
            nb078_alpha_dummy_235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0236)
                  0)))) (show (nb078_alpha_dummy_226 f) ≠ (nb078_alpha_dummy_236 f) from (by
          unfold
            nb078_alpha_dummy_236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0237
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_223) ≠ (nb078_alpha_dummy_231)
        from (by
          unfold
            nb078_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0234)
                  0)))) (show (nb078_alpha_dummy_226 f) ≠ (nb078_alpha_dummy_232 f) from (by
          unfold
            nb078_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0235
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_215) ≠ (nb078_alpha_dummy_219) from (by
          unfold nb078_alpha_dummy_219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0218) 0)))) (show (nb078_alpha_dummy_217 f) ≠
        (nb078_alpha_dummy_220 f) from (by
          unfold nb078_alpha_dummy_220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_219),
        (nb078_alpha_dummy_220 f)), ((nb078_alpha_dummy_215), (nb078_alpha_dummy_217 f)),
        ((nb078_alpha_dummy_216), (nb078_alpha_dummy_218 f)), ((nb078_alpha_dummy_208),
        (nb078_alpha_dummy_210 f)), ((nb078_alpha_dummy_207), (nb078_alpha_dummy_209 f)),
        ((nb078_alpha_dummy_213), (nb078_alpha_dummy_214 f)), ((nb078_alpha_dummy_211),
        (nb078_alpha_dummy_212 f)), ((nb078_alpha_dummy_204), (nb078_alpha_dummy_206 f)),
        ((nb078_alpha_dummy_203), (nb078_alpha_dummy_205 f)), ((nb078_alpha_dummy_000), f),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078_alpha_dummy_215) ≠
        (nb078_alpha_dummy_219) from (by
          unfold nb078_alpha_dummy_219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0218) 0)))) (show (nb078_alpha_dummy_217 f) ≠
        (nb078_alpha_dummy_220 f) from (by
          unfold nb078_alpha_dummy_220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_215) ≠ (nb078_alpha_dummy_219) from (by
          unfold nb078_alpha_dummy_219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0218) 0)))) (show (nb078_alpha_dummy_217 f) ≠
        (nb078_alpha_dummy_220 f) from (by
          unfold nb078_alpha_dummy_220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_219),
        (nb078_alpha_dummy_220 f)), ((nb078_alpha_dummy_215), (nb078_alpha_dummy_217 f)),
        ((nb078_alpha_dummy_216), (nb078_alpha_dummy_218 f)), ((nb078_alpha_dummy_208),
        (nb078_alpha_dummy_210 f)), ((nb078_alpha_dummy_207), (nb078_alpha_dummy_209 f)),
        ((nb078_alpha_dummy_213), (nb078_alpha_dummy_214 f)), ((nb078_alpha_dummy_211),
        (nb078_alpha_dummy_212 f)), ((nb078_alpha_dummy_204), (nb078_alpha_dummy_206 f)),
        ((nb078_alpha_dummy_203), (nb078_alpha_dummy_205 f)), ((nb078_alpha_dummy_000), f),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc)
        (by simp only [fv_syn_cnnc])))))))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb078_split_alpha_0021 x y f)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb078_split_alpha_0021 x y f)))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
