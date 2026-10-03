/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C068C001Block005

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C068C001Part021`. -/


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
noncomputable def nb068_split_alpha_0023 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_179), (nb068_alpha_dummy_180 f)),
        ((nb068_alpha_dummy_175), (nb068_alpha_dummy_177 f)),
        ((nb068_alpha_dummy_176), (nb068_alpha_dummy_178 f)),
        ((nb068_alpha_dummy_201), (nb068_alpha_dummy_202 f)),
        ((nb068_alpha_dummy_199), (nb068_alpha_dummy_200 f)),
        ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)),
        ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)),
        ((nb068_alpha_dummy_197), (nb068_alpha_dummy_198 f)),
        ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)),
        ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
        ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
        ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
        ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
        ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
        ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
        ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
        ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)),
        ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb068_alpha_dummy_179))
              (syn_cplc (Class.cv (nb068_alpha_dummy_175)) (syn_c1c)))
            (Wff.classMem (Class.cv (nb068_alpha_dummy_175)) (syn_cnnc)))) (syn_wa
          (Wff.classMem (Class.cv (nb068_alpha_dummy_179)) (Class.cv (nb068_alpha_dummy_175)))
          (Wff.neg (Wff.classMem (Class.cv (nb068_alpha_dummy_175)) (syn_cnnc)))))
      (Wff.imp (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb068_alpha_dummy_180 f))
              (syn_cplc (Class.cv (nb068_alpha_dummy_177 f)) (syn_c1c)))
            (Wff.classMem (Class.cv (nb068_alpha_dummy_177 f)) (syn_cnnc)))) (syn_wa
          (Wff.classMem (Class.cv (nb068_alpha_dummy_180 f))
            (Class.cv (nb068_alpha_dummy_177 f)))
          (Wff.neg (Wff.classMem (Class.cv (nb068_alpha_dummy_177 f)) (syn_cnnc))))) :=
  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068_alpha_dummy_175) ≠ (nb068_alpha_dummy_182) from (by
                          unfold nb068_alpha_dummy_182;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0174) 1))))
                      (show (nb068_alpha_dummy_177 f) ≠ (nb068_alpha_dummy_185 f) from (by
                          unfold nb068_alpha_dummy_185;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0175 f) 1))))
                      (TAlphaVar.there
                        (show (nb068_alpha_dummy_175) ≠ (nb068_alpha_dummy_181) from (by
                            unfold nb068_alpha_dummy_181;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0174) 0))))
                        (show (nb068_alpha_dummy_177 f) ≠ (nb068_alpha_dummy_184 f) from (by
                            unfold nb068_alpha_dummy_184;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0175 f) 0))))
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_175) ≠ (nb068_alpha_dummy_179) from (by
                              unfold nb068_alpha_dummy_179;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0172) 0))))
                          (show (nb068_alpha_dummy_177 f) ≠ (nb068_alpha_dummy_180 f) from (by
                              unfold nb068_alpha_dummy_180;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
                          (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb068_alpha_dummy_183), (nb068_alpha_dummy_186 f)),
                          ((nb068_alpha_dummy_182), (nb068_alpha_dummy_185 f)),
                          ((nb068_alpha_dummy_181), (nb068_alpha_dummy_184 f)),
                          ((nb068_alpha_dummy_179), (nb068_alpha_dummy_180 f)),
                          ((nb068_alpha_dummy_175), (nb068_alpha_dummy_177 f)),
                          ((nb068_alpha_dummy_176), (nb068_alpha_dummy_178 f)),
                          ((nb068_alpha_dummy_201), (nb068_alpha_dummy_202 f)),
                          ((nb068_alpha_dummy_199), (nb068_alpha_dummy_200 f)),
                          ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)),
                          ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)),
                          ((nb068_alpha_dummy_197), (nb068_alpha_dummy_198 f)),
                          ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)),
                          ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
                          ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
                          ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
                          ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
                          ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
                          ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
                          ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
                          ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)),
                          ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)),
                          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                          ((nb068_alpha_dummy_001), x),
                          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                        (syn_c1c) (by simp only [fv_syn_c1c])))
                    (TAlphaWff.neg (nb068_split_alpha_0022 x y f)))))))) (TAlphaWff.classMem
          (TAlphaClass.cv (TAlphaVar.there
              (show (nb068_alpha_dummy_175) ≠ (nb068_alpha_dummy_179) from (by
                  unfold nb068_alpha_dummy_179;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0172) 0))))
              (show (nb068_alpha_dummy_177 f) ≠ (nb068_alpha_dummy_180 f) from (by
                  unfold nb068_alpha_dummy_180;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
            [((nb068_alpha_dummy_179), (nb068_alpha_dummy_180 f)),
              ((nb068_alpha_dummy_175), (nb068_alpha_dummy_177 f)),
              ((nb068_alpha_dummy_176), (nb068_alpha_dummy_178 f)),
              ((nb068_alpha_dummy_201), (nb068_alpha_dummy_202 f)),
              ((nb068_alpha_dummy_199), (nb068_alpha_dummy_200 f)),
              ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)),
              ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)),
              ((nb068_alpha_dummy_197), (nb068_alpha_dummy_198 f)),
              ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)),
              ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
              ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
              ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
              ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
              ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
              ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
              ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
              ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)),
              ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)),
              ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
              ((nb068_alpha_dummy_001), x),
              ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
          (TAlphaVar.there (show (nb068_alpha_dummy_175) ≠ (nb068_alpha_dummy_179) from (by
                unfold nb068_alpha_dummy_179;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0172) 0))))
            (show (nb068_alpha_dummy_177 f) ≠ (nb068_alpha_dummy_180 f) from (by
                unfold nb068_alpha_dummy_180;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
            (TAlphaVar.there (show (nb068_alpha_dummy_175) ≠ (nb068_alpha_dummy_179) from (by
                  unfold nb068_alpha_dummy_179;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0172) 0))))
              (show (nb068_alpha_dummy_177 f) ≠ (nb068_alpha_dummy_180 f) from (by
                  unfold nb068_alpha_dummy_180;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
            [((nb068_alpha_dummy_179), (nb068_alpha_dummy_180 f)),
              ((nb068_alpha_dummy_175), (nb068_alpha_dummy_177 f)),
              ((nb068_alpha_dummy_176), (nb068_alpha_dummy_178 f)),
              ((nb068_alpha_dummy_201), (nb068_alpha_dummy_202 f)),
              ((nb068_alpha_dummy_199), (nb068_alpha_dummy_200 f)),
              ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)),
              ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)),
              ((nb068_alpha_dummy_197), (nb068_alpha_dummy_198 f)),
              ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)),
              ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
              ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
              ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
              ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
              ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
              ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
              ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
              ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)),
              ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)),
              ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
              ((nb068_alpha_dummy_001), x),
              ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))

@[expose]
noncomputable def nb068_split_alpha_0024 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)),
        ((nb068_alpha_dummy_197), (nb068_alpha_dummy_198 f)),
        ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)),
        ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
        ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
        ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
        ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
        ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
        ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
        ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
        ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)),
        ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.neg (Wff.all (nb068_alpha_dummy_168) (Wff.neg (syn_wa
              (Wff.classMem (Class.cv (nb068_alpha_dummy_168))
                (Class.cv (nb068_alpha_dummy_125)))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_167))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_168))) (syn_csn (syn_c0c))))))))
      (Wff.neg (Wff.all (nb068_alpha_dummy_170 f) (Wff.neg (syn_wa
              (Wff.classMem (Class.cv (nb068_alpha_dummy_170 f))
                (Class.cv (nb068_alpha_dummy_127 f)))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))
                  (syn_csn (syn_c0c)))))))) :=
  (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there
            (show (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_168) from (by
                unfold nb068_alpha_dummy_168;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0192) 1))))
            (show (nb068_alpha_dummy_127 f) ≠ (nb068_alpha_dummy_170 f) from (by
                unfold nb068_alpha_dummy_170;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0194 f) 1))))
            (TAlphaVar.there (show (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_167) from (by
                  unfold nb068_alpha_dummy_167;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0192) 0))))
              (show (nb068_alpha_dummy_127 f) ≠ (nb068_alpha_dummy_169 f) from (by
                  unfold nb068_alpha_dummy_169;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0194 f) 0))))
              (TAlphaVar.there (show (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_197) from (by
                    unfold nb068_alpha_dummy_197;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0196) 0))))
                (show (nb068_alpha_dummy_127 f) ≠ (nb068_alpha_dummy_198 f) from (by
                    unfold nb068_alpha_dummy_198;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0197 f) 0))))
                (TAlphaVar.there (show (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_171) from
                    (by
                      unfold nb068_alpha_dummy_171;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0193) 0))))
                  (show (nb068_alpha_dummy_127 f) ≠ (nb068_alpha_dummy_172 f) from (by
                      unfold nb068_alpha_dummy_172;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0195 f) 0))))
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_000))).fv)
                      (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
                    (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_126))).fv ∪
                ((Class.cv (nb068_alpha_dummy_125))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb068_alpha_dummy_128 f))).fv ∪
                ((Class.cv (nb068_alpha_dummy_127 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb068_alpha_dummy_168) ≠ (nb068_alpha_dummy_175) from (by
                                        unfold nb068_alpha_dummy_175;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0170)
                                                0)))) (show (nb068_alpha_dummy_170 f) ≠
                                        (nb068_alpha_dummy_177 f) from (by
                                        unfold nb068_alpha_dummy_177;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0171 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068_alpha_dummy_168) ≠ (nb068_alpha_dummy_176) from
                                        (by
                                          unfold nb068_alpha_dummy_176;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0170)
                                                  1)))) (show (nb068_alpha_dummy_170 f) ≠
        (nb068_alpha_dummy_178 f) from (by
                                          unfold nb068_alpha_dummy_178;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0171 f) 1))))
                                      (TAlphaVar.there (show (nb068_alpha_dummy_168) ≠
        (nb068_alpha_dummy_201) from (by
          unfold nb068_alpha_dummy_201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0200) 0)))) (show (nb068_alpha_dummy_170 f) ≠
        (nb068_alpha_dummy_202 f) from (by
          unfold nb068_alpha_dummy_202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0201 f) 0)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_168) ≠ (nb068_alpha_dummy_199) from (by
          unfold nb068_alpha_dummy_199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0198) 0)))) (show (nb068_alpha_dummy_170 f) ≠
        (nb068_alpha_dummy_200 f) from (by
          unfold nb068_alpha_dummy_200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0199 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb068_alpha_dummy_168))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb068_alpha_dummy_170 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _)))
                                (TAlphaClass.cab (nb068_split_alpha_0023 x y f)))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb068_alpha_dummy_168) ≠ (nb068_alpha_dummy_175) from (by
                                        unfold nb068_alpha_dummy_175;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0170)
                                                0)))) (show (nb068_alpha_dummy_170 f) ≠
                                        (nb068_alpha_dummy_177 f) from (by
                                        unfold nb068_alpha_dummy_177;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0171 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068_alpha_dummy_168) ≠ (nb068_alpha_dummy_176) from
                                        (by
                                          unfold nb068_alpha_dummy_176;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0170)
                                                  1)))) (show (nb068_alpha_dummy_170 f) ≠
        (nb068_alpha_dummy_178 f) from (by
                                          unfold nb068_alpha_dummy_178;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0171 f) 1))))
                                      (TAlphaVar.there (show (nb068_alpha_dummy_168) ≠
        (nb068_alpha_dummy_201) from (by
          unfold nb068_alpha_dummy_201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0200) 0)))) (show (nb068_alpha_dummy_170 f) ≠
        (nb068_alpha_dummy_202 f) from (by
          unfold nb068_alpha_dummy_202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0201 f) 0)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_168) ≠ (nb068_alpha_dummy_199) from (by
          unfold nb068_alpha_dummy_199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0198) 0)))) (show (nb068_alpha_dummy_170 f) ≠
        (nb068_alpha_dummy_200 f) from (by
          unfold nb068_alpha_dummy_200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0199 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb068_alpha_dummy_168))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb068_alpha_dummy_170 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _)))
                                (TAlphaClass.cab (nb068_split_alpha_0023 x y f)))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb068_alpha_dummy_199), (nb068_alpha_dummy_200 f)),
                    ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)),
                    ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)),
                    ((nb068_alpha_dummy_197), (nb068_alpha_dummy_198 f)),
                    ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)),
                    ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
                    ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
                    ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
                    ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
                    ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
                    ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
                    ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
                    ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)),
                    ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)),
                    ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                    ((nb068_alpha_dummy_001), x),
                    ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                  (syn_ccompl (syn_csn (syn_c0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

@[expose]
noncomputable def nb068_split_alpha_0025 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
        ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
        ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
        ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
        ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
        ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
        ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
        ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)),
        ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.classMem
        (syn_cop (Class.cv (nb068_alpha_dummy_126)) (Class.cv (nb068_alpha_dummy_125)))
        (Class.cv (nb068_alpha_dummy_000)))
      (Wff.classMem (syn_cop (Class.cv (nb068_alpha_dummy_128 f))
          (Class.cv (nb068_alpha_dummy_127 f))) (Class.cv f)) :=
  (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_168) from (by
                                    unfold nb068_alpha_dummy_168;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0164) 1)))) (show
                                  (nb068_alpha_dummy_128 f) ≠ (nb068_alpha_dummy_170 f) from (by
                                    unfold nb068_alpha_dummy_170;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0166 f)
                                            1)))) (TAlphaVar.there
                                  (show (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_167) from
                                    (by
                                      unfold nb068_alpha_dummy_167;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0164)
                                              0)))) (show
                                    (nb068_alpha_dummy_128 f) ≠ (nb068_alpha_dummy_169 f) from
                                    (by
                                      unfold nb068_alpha_dummy_169;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0166 f)
                                              0)))) (TAlphaVar.there (show
                                      (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_173) from (by
                                        unfold nb068_alpha_dummy_173;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0168)
                                                0)))) (show (nb068_alpha_dummy_128 f) ≠
                                        (nb068_alpha_dummy_174 f) from (by
                                        unfold nb068_alpha_dummy_174;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0169 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_171) from
                                        (by
                                          unfold nb068_alpha_dummy_171;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0165)
                                                  0)))) (show (nb068_alpha_dummy_128 f) ≠
        (nb068_alpha_dummy_172 f) from (by
                                          unfold nb068_alpha_dummy_172;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0167 f) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_126))).fv ∪
                                    ((Class.cv (nb068_alpha_dummy_125))).fv) (by decide))
                                (freshVar_injective (((Class.cv (nb068_alpha_dummy_128 f))).fv ∪
                                    ((Class.cv (nb068_alpha_dummy_127 f))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb068_alpha_dummy_168) ≠
        (nb068_alpha_dummy_175) from (by
          unfold nb068_alpha_dummy_175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0170) 0)))) (show (nb068_alpha_dummy_170 f) ≠
        (nb068_alpha_dummy_177 f) from (by
          unfold nb068_alpha_dummy_177;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0171 f) 0)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_168) ≠ (nb068_alpha_dummy_176) from (by
          unfold nb068_alpha_dummy_176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0170) 1)))) (show (nb068_alpha_dummy_170 f) ≠
        (nb068_alpha_dummy_178 f) from (by
          unfold nb068_alpha_dummy_178;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0171 f) 1)))) (TAlphaVar.here _ _ _)))))
                                  (nb068_split_alpha_0021 x y f)))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_168) from (by
                                    unfold nb068_alpha_dummy_168;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0164) 1)))) (show
                                  (nb068_alpha_dummy_128 f) ≠ (nb068_alpha_dummy_170 f) from (by
                                    unfold nb068_alpha_dummy_170;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0166 f)
                                            1)))) (TAlphaVar.there
                                  (show (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_167) from
                                    (by
                                      unfold nb068_alpha_dummy_167;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0164)
                                              0)))) (show
                                    (nb068_alpha_dummy_128 f) ≠ (nb068_alpha_dummy_169 f) from
                                    (by
                                      unfold nb068_alpha_dummy_169;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0166 f)
                                              0)))) (TAlphaVar.there (show
                                      (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_173) from (by
                                        unfold nb068_alpha_dummy_173;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0168)
                                                0)))) (show (nb068_alpha_dummy_128 f) ≠
                                        (nb068_alpha_dummy_174 f) from (by
                                        unfold nb068_alpha_dummy_174;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0169 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_171) from
                                        (by
                                          unfold nb068_alpha_dummy_171;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0165)
                                                  0)))) (show (nb068_alpha_dummy_128 f) ≠
        (nb068_alpha_dummy_172 f) from (by
                                          unfold nb068_alpha_dummy_172;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0167 f) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_126))).fv ∪
                                    ((Class.cv (nb068_alpha_dummy_125))).fv) (by decide))
                                (freshVar_injective (((Class.cv (nb068_alpha_dummy_128 f))).fv ∪
                                    ((Class.cv (nb068_alpha_dummy_127 f))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb068_alpha_dummy_168) ≠
        (nb068_alpha_dummy_175) from (by
          unfold nb068_alpha_dummy_175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0170) 0)))) (show (nb068_alpha_dummy_170 f) ≠
        (nb068_alpha_dummy_177 f) from (by
          unfold nb068_alpha_dummy_177;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0171 f) 0)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_168) ≠ (nb068_alpha_dummy_176) from (by
          unfold nb068_alpha_dummy_176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0170) 1)))) (show (nb068_alpha_dummy_170 f) ≠
        (nb068_alpha_dummy_178 f) from (by
          unfold nb068_alpha_dummy_178;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0171 f) 1)))) (TAlphaVar.here _ _ _)))))
                                  (nb068_split_alpha_0021 x y f)))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.cab (nb068_split_alpha_0024 x y f)))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.cab (nb068_split_alpha_0024 x y f)))))))))) (TAlphaClass.cv
      (TAlphaVar.there (show (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_126) from (by
            unfold nb068_alpha_dummy_126;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0212) 1))))
        (show f ≠ (nb068_alpha_dummy_128 f) from (by
            unfold nb068_alpha_dummy_128;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0213 f) 1))))
        (TAlphaVar.there (show (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_125) from (by
              unfold nb068_alpha_dummy_125;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0212) 0))))
          (show f ≠ (nb068_alpha_dummy_127 f) from (by
              unfold nb068_alpha_dummy_127;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0213 f) 0))))
          (TAlphaVar.there (show (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_129) from (by
                unfold nb068_alpha_dummy_129;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0210) 0))))
            (show f ≠ (nb068_alpha_dummy_130 f) from (by
                unfold nb068_alpha_dummy_130;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0211 f) 0))))
            (TAlphaVar.there (show (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_047) from (by
                  unfold nb068_alpha_dummy_047;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0206) 2))))
              (show f ≠ (nb068_alpha_dummy_050 f) from (by
                  unfold nb068_alpha_dummy_050;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0208 f) 2))))
              (TAlphaVar.there (show (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_046) from (by
                    unfold nb068_alpha_dummy_046;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0206) 1))))
                (show f ≠ (nb068_alpha_dummy_049 f) from (by
                    unfold nb068_alpha_dummy_049;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0208 f) 1))))
                (TAlphaVar.there (show (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_045) from
                    (by
                      unfold nb068_alpha_dummy_045;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0206) 0))))
                  (show f ≠ (nb068_alpha_dummy_048 f) from (by
                      unfold nb068_alpha_dummy_048;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0208 f) 0))))
                  (TAlphaVar.there (show (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_051) from
                      (by
                        unfold nb068_alpha_dummy_051;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0207) 0))))
                    (show f ≠ (nb068_alpha_dummy_052 f) from (by
                        unfold nb068_alpha_dummy_052;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0209 f) 0)))) (TAlphaVar.there
                      (show (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_043) from (by
                          unfold nb068_alpha_dummy_043;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0204) 0))))
                      (show f ≠ (nb068_alpha_dummy_044 f) from (by
                          unfold nb068_alpha_dummy_044;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0205 f) 0))))
                      (TAlphaVar.there
                        (show (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_041) from (by
                            unfold nb068_alpha_dummy_041;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0202) 0))))
                        (show f ≠ (nb068_alpha_dummy_042 f) from (by
                            unfold nb068_alpha_dummy_042;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0203 f) 0))))
                        (TAlphaVar.here _ _ _))))))))))))

@[expose]
noncomputable def nb068_split_alpha_0026 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
        ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
        ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
        ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
        ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
        ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
        ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)),
        ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.all (nb068_alpha_dummy_126) (Wff.neg (syn_wa
            (Wff.classEq (Class.cv (nb068_alpha_dummy_129))
              (syn_cop (Class.cv (nb068_alpha_dummy_125)) (Class.cv (nb068_alpha_dummy_126))))
            (syn_wbr (Class.cv (nb068_alpha_dummy_126)) (Class.cv (nb068_alpha_dummy_000))
              (Class.cv (nb068_alpha_dummy_125))))))
      (Wff.all (nb068_alpha_dummy_128 f) (Wff.neg (syn_wa
            (Wff.classEq (Class.cv (nb068_alpha_dummy_130 f))
              (syn_cop (Class.cv (nb068_alpha_dummy_127 f))
                (Class.cv (nb068_alpha_dummy_128 f))))
            (syn_wbr (Class.cv (nb068_alpha_dummy_128 f)) (Class.cv f)
              (Class.cv (nb068_alpha_dummy_127 f)))))) :=
  (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
            (TAlphaVar.there (Ne.symm
                (show (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_129) from (by
                    unfold nb068_alpha_dummy_129;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0124) 0)))))
              (Ne.symm (show (nb068_alpha_dummy_128 f) ≠ (nb068_alpha_dummy_130 f) from (by
                    unfold nb068_alpha_dummy_130;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0125 f) 0)))))
              (TAlphaVar.there (Ne.symm
                  (show (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_129) from (by
                      unfold nb068_alpha_dummy_129;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0122) 0)))))
                (Ne.symm (show (nb068_alpha_dummy_127 f) ≠ (nb068_alpha_dummy_130 f) from (by
                      unfold nb068_alpha_dummy_130;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0123 f) 0)))))
                (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_132) from
                                        (by
                                          unfold nb068_alpha_dummy_132;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0126)
                                                  1)))) (show (nb068_alpha_dummy_127 f) ≠
        (nb068_alpha_dummy_134 f) from (by
                                          unfold nb068_alpha_dummy_134;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0128 f) 1))))
                                      (TAlphaVar.there (show (nb068_alpha_dummy_125) ≠
        (nb068_alpha_dummy_131) from (by
          unfold nb068_alpha_dummy_131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0126) 0)))) (show (nb068_alpha_dummy_127 f) ≠
        (nb068_alpha_dummy_133 f) from (by
          unfold nb068_alpha_dummy_133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0128 f) 0)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_137) from (by
          unfold nb068_alpha_dummy_137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0130) 0)))) (show (nb068_alpha_dummy_127 f) ≠
        (nb068_alpha_dummy_138 f) from (by
          unfold nb068_alpha_dummy_138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0131 f) 0)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_135) from (by
          unfold nb068_alpha_dummy_135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0127) 0)))) (show (nb068_alpha_dummy_127 f) ≠
        (nb068_alpha_dummy_136 f) from (by
          unfold nb068_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0129 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb068_alpha_dummy_000))).fv) (by decide))
        (freshVar_injective (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                      (freshVar_injective
                                        (((Class.cv (nb068_alpha_dummy_125))).fv ∪
        ((Class.cv (nb068_alpha_dummy_126))).fv) (by decide)) (freshVar_injective
                                        (((Class.cv (nb068_alpha_dummy_127 f))).fv ∪
        ((Class.cv (nb068_alpha_dummy_128 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb068_alpha_dummy_132) ≠ (nb068_alpha_dummy_139) from (by
          unfold nb068_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 0)))) (show (nb068_alpha_dummy_134 f) ≠
        (nb068_alpha_dummy_141 f) from (by
          unfold nb068_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f) 0)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_132) ≠ (nb068_alpha_dummy_140) from (by
          unfold nb068_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 1)))) (show (nb068_alpha_dummy_134 f) ≠
        (nb068_alpha_dummy_142 f) from (by
          unfold nb068_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f)
                  1)))) (TAlphaVar.here _ _ _))))) (nb068_split_alpha_0016 x y f)))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_132) from
                                        (by
                                          unfold nb068_alpha_dummy_132;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0126)
                                                  1)))) (show (nb068_alpha_dummy_127 f) ≠
        (nb068_alpha_dummy_134 f) from (by
                                          unfold nb068_alpha_dummy_134;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0128 f) 1))))
                                      (TAlphaVar.there (show (nb068_alpha_dummy_125) ≠
        (nb068_alpha_dummy_131) from (by
          unfold nb068_alpha_dummy_131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0126) 0)))) (show (nb068_alpha_dummy_127 f) ≠
        (nb068_alpha_dummy_133 f) from (by
          unfold nb068_alpha_dummy_133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0128 f) 0)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_137) from (by
          unfold nb068_alpha_dummy_137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0130) 0)))) (show (nb068_alpha_dummy_127 f) ≠
        (nb068_alpha_dummy_138 f) from (by
          unfold nb068_alpha_dummy_138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0131 f) 0)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_135) from (by
          unfold nb068_alpha_dummy_135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0127) 0)))) (show (nb068_alpha_dummy_127 f) ≠
        (nb068_alpha_dummy_136 f) from (by
          unfold nb068_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0129 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb068_alpha_dummy_000))).fv) (by decide))
        (freshVar_injective (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                      (freshVar_injective
                                        (((Class.cv (nb068_alpha_dummy_125))).fv ∪
        ((Class.cv (nb068_alpha_dummy_126))).fv) (by decide)) (freshVar_injective
                                        (((Class.cv (nb068_alpha_dummy_127 f))).fv ∪
        ((Class.cv (nb068_alpha_dummy_128 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb068_alpha_dummy_132) ≠ (nb068_alpha_dummy_139) from (by
          unfold nb068_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 0)))) (show (nb068_alpha_dummy_134 f) ≠
        (nb068_alpha_dummy_141 f) from (by
          unfold nb068_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f) 0)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_132) ≠ (nb068_alpha_dummy_140) from (by
          unfold nb068_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 1)))) (show (nb068_alpha_dummy_134 f) ≠
        (nb068_alpha_dummy_142 f) from (by
          unfold nb068_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f)
                  1)))) (TAlphaVar.here _ _ _))))) (nb068_split_alpha_0016 x y f)))))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0019 x y f)))))))))
        (nb068_split_alpha_0025 x y f))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part022`. -/


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
noncomputable def nb068_split_alpha_0027 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_219), (nb068_alpha_dummy_222 f)),
        ((nb068_alpha_dummy_218), (nb068_alpha_dummy_221 f)),
        ((nb068_alpha_dummy_217), (nb068_alpha_dummy_220 f)),
        ((nb068_alpha_dummy_215), (nb068_alpha_dummy_216 f)),
        ((nb068_alpha_dummy_211), (nb068_alpha_dummy_213 f)),
        ((nb068_alpha_dummy_212), (nb068_alpha_dummy_214 f)),
        ((nb068_alpha_dummy_204), (nb068_alpha_dummy_206 f)),
        ((nb068_alpha_dummy_203), (nb068_alpha_dummy_205 f)),
        ((nb068_alpha_dummy_209), (nb068_alpha_dummy_210 f)),
        ((nb068_alpha_dummy_207), (nb068_alpha_dummy_208 f)),
        ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
        ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
        ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
        ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
        ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)),
        ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb068_alpha_dummy_218)) (Class.cv (nb068_alpha_dummy_219)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_217))
            (syn_cun (Class.cv (nb068_alpha_dummy_218)) (Class.cv (nb068_alpha_dummy_219))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_221 f))
            (Class.cv (nb068_alpha_dummy_222 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_220 f))
            (syn_cun (Class.cv (nb068_alpha_dummy_221 f))
              (Class.cv (nb068_alpha_dummy_222 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_218) ≠ (nb068_alpha_dummy_225) from (by
                              unfold nb068_alpha_dummy_225;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0228) 0))))
                          (show (nb068_alpha_dummy_221 f) ≠ (nb068_alpha_dummy_226 f) from (by
                              unfold nb068_alpha_dummy_226;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0229 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_218) ≠ (nb068_alpha_dummy_223) from (by
                                unfold nb068_alpha_dummy_223;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0226) 0))))
                            (show (nb068_alpha_dummy_221 f) ≠ (nb068_alpha_dummy_224 f) from (by
                                unfold nb068_alpha_dummy_224;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0227 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_211))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_213 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_219) ≠ (nb068_alpha_dummy_225) from (by
                              unfold nb068_alpha_dummy_225;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0232) 0))))
                          (show (nb068_alpha_dummy_222 f) ≠ (nb068_alpha_dummy_226 f) from (by
                              unfold nb068_alpha_dummy_226;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0233 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_219) ≠ (nb068_alpha_dummy_223) from (by
                                unfold nb068_alpha_dummy_223;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0230) 0))))
                            (show (nb068_alpha_dummy_222 f) ≠ (nb068_alpha_dummy_224 f) from (by
                                unfold nb068_alpha_dummy_224;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0231 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_218) ≠ (nb068_alpha_dummy_225) from (by
                              unfold nb068_alpha_dummy_225;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0228) 0))))
                          (show (nb068_alpha_dummy_221 f) ≠ (nb068_alpha_dummy_226 f) from (by
                              unfold nb068_alpha_dummy_226;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0229 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_218) ≠ (nb068_alpha_dummy_223) from (by
                                unfold nb068_alpha_dummy_223;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0226) 0))))
                            (show (nb068_alpha_dummy_221 f) ≠ (nb068_alpha_dummy_224 f) from (by
                                unfold nb068_alpha_dummy_224;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0227 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_211))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_213 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_219) ≠ (nb068_alpha_dummy_225) from (by
                              unfold nb068_alpha_dummy_225;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0232) 0))))
                          (show (nb068_alpha_dummy_222 f) ≠ (nb068_alpha_dummy_226 f) from (by
                              unfold nb068_alpha_dummy_226;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0233 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_219) ≠ (nb068_alpha_dummy_223) from (by
                                unfold nb068_alpha_dummy_223;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0230) 0))))
                            (show (nb068_alpha_dummy_222 f) ≠ (nb068_alpha_dummy_224 f) from (by
                                unfold nb068_alpha_dummy_224;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0231 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb068_alpha_dummy_219), (nb068_alpha_dummy_222 f)),
          ((nb068_alpha_dummy_218), (nb068_alpha_dummy_221 f)),
          ((nb068_alpha_dummy_217), (nb068_alpha_dummy_220 f)),
          ((nb068_alpha_dummy_215), (nb068_alpha_dummy_216 f)),
          ((nb068_alpha_dummy_211), (nb068_alpha_dummy_213 f)),
          ((nb068_alpha_dummy_212), (nb068_alpha_dummy_214 f)),
          ((nb068_alpha_dummy_204), (nb068_alpha_dummy_206 f)),
          ((nb068_alpha_dummy_203), (nb068_alpha_dummy_205 f)),
          ((nb068_alpha_dummy_209), (nb068_alpha_dummy_210 f)),
          ((nb068_alpha_dummy_207), (nb068_alpha_dummy_208 f)),
          ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
          ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
          ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
          ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
          ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)),
          ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)),
          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
          ((nb068_alpha_dummy_001), x),
          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_211))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068_alpha_dummy_213 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_211))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_213 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_218) ≠ (nb068_alpha_dummy_229) from (by
                                unfold nb068_alpha_dummy_229;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0236) 0))))
                            (show (nb068_alpha_dummy_221 f) ≠ (nb068_alpha_dummy_230 f) from (by
                                unfold nb068_alpha_dummy_230;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0237 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_218) ≠ (nb068_alpha_dummy_227) from (by
                                  unfold nb068_alpha_dummy_227;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0234) 0))))
                              (show (nb068_alpha_dummy_221 f) ≠ (nb068_alpha_dummy_228 f) from
                                (by
                                  unfold nb068_alpha_dummy_228;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0235 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_211))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_213 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_218) ≠ (nb068_alpha_dummy_229) from (by
                                unfold nb068_alpha_dummy_229;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0236) 0))))
                            (show (nb068_alpha_dummy_221 f) ≠ (nb068_alpha_dummy_230 f) from (by
                                unfold nb068_alpha_dummy_230;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0237 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_218) ≠ (nb068_alpha_dummy_227) from (by
                                  unfold nb068_alpha_dummy_227;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0234) 0))))
                              (show (nb068_alpha_dummy_221 f) ≠ (nb068_alpha_dummy_228 f) from
                                (by
                                  unfold nb068_alpha_dummy_228;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0235 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_211))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_213 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_219) ≠ (nb068_alpha_dummy_231) from (by
                                unfold nb068_alpha_dummy_231;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0240) 0))))
                            (show (nb068_alpha_dummy_222 f) ≠ (nb068_alpha_dummy_232 f) from (by
                                unfold nb068_alpha_dummy_232;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0241 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_219) ≠ (nb068_alpha_dummy_227) from (by
                                  unfold nb068_alpha_dummy_227;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0238) 0))))
                              (show (nb068_alpha_dummy_222 f) ≠ (nb068_alpha_dummy_228 f) from
                                (by
                                  unfold nb068_alpha_dummy_228;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0239 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_219) ≠ (nb068_alpha_dummy_231) from (by
                                unfold nb068_alpha_dummy_231;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0240) 0))))
                            (show (nb068_alpha_dummy_222 f) ≠ (nb068_alpha_dummy_232 f) from (by
                                unfold nb068_alpha_dummy_232;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0241 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_219) ≠ (nb068_alpha_dummy_227) from (by
                                  unfold nb068_alpha_dummy_227;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0238) 0))))
                              (show (nb068_alpha_dummy_222 f) ≠ (nb068_alpha_dummy_228 f) from
                                (by
                                  unfold nb068_alpha_dummy_228;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0239 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb068_split_alpha_0028 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_211), (nb068_alpha_dummy_213 f)),
        ((nb068_alpha_dummy_212), (nb068_alpha_dummy_214 f)),
        ((nb068_alpha_dummy_204), (nb068_alpha_dummy_206 f)),
        ((nb068_alpha_dummy_203), (nb068_alpha_dummy_205 f)),
        ((nb068_alpha_dummy_209), (nb068_alpha_dummy_210 f)),
        ((nb068_alpha_dummy_207), (nb068_alpha_dummy_208 f)),
        ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
        ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
        ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
        ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
        ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)),
        ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_211))
          (Class.cv (nb068_alpha_dummy_204))) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_212))
            (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_211)) (syn_cnnc))
              (syn_cplc (Class.cv (nb068_alpha_dummy_211)) (syn_c1c))
              (Class.cv (nb068_alpha_dummy_211))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_213 f))
          (Class.cv (nb068_alpha_dummy_206 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_214 f))
            (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_213 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb068_alpha_dummy_213 f)) (syn_c1c))
              (Class.cv (nb068_alpha_dummy_213 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068_alpha_dummy_204) ≠ (nb068_alpha_dummy_211) from (by
              unfold nb068_alpha_dummy_211;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0220) 0))))
          (show (nb068_alpha_dummy_206 f) ≠ (nb068_alpha_dummy_213 f) from (by
              unfold nb068_alpha_dummy_213;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0221 f) 0))))
          (TAlphaVar.there (show (nb068_alpha_dummy_204) ≠ (nb068_alpha_dummy_212) from (by
                unfold nb068_alpha_dummy_212;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0220) 1))))
            (show (nb068_alpha_dummy_206 f) ≠ (nb068_alpha_dummy_214 f) from (by
                unfold nb068_alpha_dummy_214;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0221 f) 1))))
            (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_204))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_206 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068_alpha_dummy_211) ≠ (nb068_alpha_dummy_218) from (by
                                  unfold nb068_alpha_dummy_218;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0224) 1))))
                              (show (nb068_alpha_dummy_213 f) ≠ (nb068_alpha_dummy_221 f) from
                                (by
                                  unfold nb068_alpha_dummy_221;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0225 f) 1))))
                              (TAlphaVar.there
                                (show (nb068_alpha_dummy_211) ≠ (nb068_alpha_dummy_217) from (by
                                    unfold nb068_alpha_dummy_217;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0224) 0)))) (show
                                  (nb068_alpha_dummy_213 f) ≠ (nb068_alpha_dummy_220 f) from (by
                                    unfold nb068_alpha_dummy_220;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0225 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb068_alpha_dummy_211) ≠ (nb068_alpha_dummy_215) from
                                    (by
                                      unfold nb068_alpha_dummy_215;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0222)
                                              0)))) (show
                                    (nb068_alpha_dummy_213 f) ≠ (nb068_alpha_dummy_216 f) from
                                    (by
                                      unfold nb068_alpha_dummy_216;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0223 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb068_alpha_dummy_219), (nb068_alpha_dummy_222 f)),
                                  ((nb068_alpha_dummy_218), (nb068_alpha_dummy_221 f)),
                                  ((nb068_alpha_dummy_217), (nb068_alpha_dummy_220 f)),
                                  ((nb068_alpha_dummy_215), (nb068_alpha_dummy_216 f)),
                                  ((nb068_alpha_dummy_211), (nb068_alpha_dummy_213 f)),
                                  ((nb068_alpha_dummy_212), (nb068_alpha_dummy_214 f)),
                                  ((nb068_alpha_dummy_204), (nb068_alpha_dummy_206 f)),
                                  ((nb068_alpha_dummy_203), (nb068_alpha_dummy_205 f)),
                                  ((nb068_alpha_dummy_209), (nb068_alpha_dummy_210 f)),
                                  ((nb068_alpha_dummy_207), (nb068_alpha_dummy_208 f)),
                                  ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
                                  ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
                                  ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
                                  ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
                                  ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)),
                                  ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)),
                                  ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                                  ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003),
                                    (nb068_alpha_dummy_004 x y f))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb068_split_alpha_0027 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb068_alpha_dummy_211) ≠ (nb068_alpha_dummy_215) from (by
                          unfold nb068_alpha_dummy_215;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0222) 0))))
                      (show (nb068_alpha_dummy_213 f) ≠ (nb068_alpha_dummy_216 f) from (by
                          unfold nb068_alpha_dummy_216;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0223 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb068_alpha_dummy_215), (nb068_alpha_dummy_216 f)),
                      ((nb068_alpha_dummy_211), (nb068_alpha_dummy_213 f)),
                      ((nb068_alpha_dummy_212), (nb068_alpha_dummy_214 f)),
                      ((nb068_alpha_dummy_204), (nb068_alpha_dummy_206 f)),
                      ((nb068_alpha_dummy_203), (nb068_alpha_dummy_205 f)),
                      ((nb068_alpha_dummy_209), (nb068_alpha_dummy_210 f)),
                      ((nb068_alpha_dummy_207), (nb068_alpha_dummy_208 f)),
                      ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
                      ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
                      ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
                      ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
                      ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)),
                      ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)),
                      ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                      ((nb068_alpha_dummy_001), x),
                      ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068_alpha_dummy_211) ≠ (nb068_alpha_dummy_215) from
                      (by
                        unfold nb068_alpha_dummy_215;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0222) 0))))
                    (show (nb068_alpha_dummy_213 f) ≠ (nb068_alpha_dummy_216 f) from (by
                        unfold nb068_alpha_dummy_216;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0223 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068_alpha_dummy_211) ≠ (nb068_alpha_dummy_215) from (by
                          unfold nb068_alpha_dummy_215;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0222) 0))))
                      (show (nb068_alpha_dummy_213 f) ≠ (nb068_alpha_dummy_216 f) from (by
                          unfold nb068_alpha_dummy_216;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0223 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb068_alpha_dummy_215), (nb068_alpha_dummy_216 f)),
                      ((nb068_alpha_dummy_211), (nb068_alpha_dummy_213 f)),
                      ((nb068_alpha_dummy_212), (nb068_alpha_dummy_214 f)),
                      ((nb068_alpha_dummy_204), (nb068_alpha_dummy_206 f)),
                      ((nb068_alpha_dummy_203), (nb068_alpha_dummy_205 f)),
                      ((nb068_alpha_dummy_209), (nb068_alpha_dummy_210 f)),
                      ((nb068_alpha_dummy_207), (nb068_alpha_dummy_208 f)),
                      ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
                      ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
                      ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
                      ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
                      ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)),
                      ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)),
                      ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                      ((nb068_alpha_dummy_001), x),
                      ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb068_split_alpha_0029 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_219), (nb068_alpha_dummy_222 f)),
        ((nb068_alpha_dummy_218), (nb068_alpha_dummy_221 f)),
        ((nb068_alpha_dummy_217), (nb068_alpha_dummy_220 f)),
        ((nb068_alpha_dummy_215), (nb068_alpha_dummy_216 f)),
        ((nb068_alpha_dummy_211), (nb068_alpha_dummy_213 f)),
        ((nb068_alpha_dummy_212), (nb068_alpha_dummy_214 f)),
        ((nb068_alpha_dummy_237), (nb068_alpha_dummy_238 f)),
        ((nb068_alpha_dummy_235), (nb068_alpha_dummy_236 f)),
        ((nb068_alpha_dummy_204), (nb068_alpha_dummy_206 f)),
        ((nb068_alpha_dummy_203), (nb068_alpha_dummy_205 f)),
        ((nb068_alpha_dummy_233), (nb068_alpha_dummy_234 f)),
        ((nb068_alpha_dummy_207), (nb068_alpha_dummy_208 f)),
        ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
        ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
        ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
        ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
        ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)),
        ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb068_alpha_dummy_218)) (Class.cv (nb068_alpha_dummy_219)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_217))
            (syn_cun (Class.cv (nb068_alpha_dummy_218)) (Class.cv (nb068_alpha_dummy_219))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_221 f))
            (Class.cv (nb068_alpha_dummy_222 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_220 f))
            (syn_cun (Class.cv (nb068_alpha_dummy_221 f))
              (Class.cv (nb068_alpha_dummy_222 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_218) ≠ (nb068_alpha_dummy_225) from (by
                              unfold nb068_alpha_dummy_225;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0228) 0))))
                          (show (nb068_alpha_dummy_221 f) ≠ (nb068_alpha_dummy_226 f) from (by
                              unfold nb068_alpha_dummy_226;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0229 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_218) ≠ (nb068_alpha_dummy_223) from (by
                                unfold nb068_alpha_dummy_223;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0226) 0))))
                            (show (nb068_alpha_dummy_221 f) ≠ (nb068_alpha_dummy_224 f) from (by
                                unfold nb068_alpha_dummy_224;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0227 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_211))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_213 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_219) ≠ (nb068_alpha_dummy_225) from (by
                              unfold nb068_alpha_dummy_225;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0232) 0))))
                          (show (nb068_alpha_dummy_222 f) ≠ (nb068_alpha_dummy_226 f) from (by
                              unfold nb068_alpha_dummy_226;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0233 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_219) ≠ (nb068_alpha_dummy_223) from (by
                                unfold nb068_alpha_dummy_223;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0230) 0))))
                            (show (nb068_alpha_dummy_222 f) ≠ (nb068_alpha_dummy_224 f) from (by
                                unfold nb068_alpha_dummy_224;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0231 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_218) ≠ (nb068_alpha_dummy_225) from (by
                              unfold nb068_alpha_dummy_225;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0228) 0))))
                          (show (nb068_alpha_dummy_221 f) ≠ (nb068_alpha_dummy_226 f) from (by
                              unfold nb068_alpha_dummy_226;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0229 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_218) ≠ (nb068_alpha_dummy_223) from (by
                                unfold nb068_alpha_dummy_223;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0226) 0))))
                            (show (nb068_alpha_dummy_221 f) ≠ (nb068_alpha_dummy_224 f) from (by
                                unfold nb068_alpha_dummy_224;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0227 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_211))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_213 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_219) ≠ (nb068_alpha_dummy_225) from (by
                              unfold nb068_alpha_dummy_225;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0232) 0))))
                          (show (nb068_alpha_dummy_222 f) ≠ (nb068_alpha_dummy_226 f) from (by
                              unfold nb068_alpha_dummy_226;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0233 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_219) ≠ (nb068_alpha_dummy_223) from (by
                                unfold nb068_alpha_dummy_223;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0230) 0))))
                            (show (nb068_alpha_dummy_222 f) ≠ (nb068_alpha_dummy_224 f) from (by
                                unfold nb068_alpha_dummy_224;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0231 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb068_alpha_dummy_219), (nb068_alpha_dummy_222 f)),
          ((nb068_alpha_dummy_218), (nb068_alpha_dummy_221 f)),
          ((nb068_alpha_dummy_217), (nb068_alpha_dummy_220 f)),
          ((nb068_alpha_dummy_215), (nb068_alpha_dummy_216 f)),
          ((nb068_alpha_dummy_211), (nb068_alpha_dummy_213 f)),
          ((nb068_alpha_dummy_212), (nb068_alpha_dummy_214 f)),
          ((nb068_alpha_dummy_237), (nb068_alpha_dummy_238 f)),
          ((nb068_alpha_dummy_235), (nb068_alpha_dummy_236 f)),
          ((nb068_alpha_dummy_204), (nb068_alpha_dummy_206 f)),
          ((nb068_alpha_dummy_203), (nb068_alpha_dummy_205 f)),
          ((nb068_alpha_dummy_233), (nb068_alpha_dummy_234 f)),
          ((nb068_alpha_dummy_207), (nb068_alpha_dummy_208 f)),
          ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
          ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
          ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
          ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
          ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)),
          ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)),
          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
          ((nb068_alpha_dummy_001), x),
          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_211))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068_alpha_dummy_213 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_211))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_213 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_218) ≠ (nb068_alpha_dummy_229) from (by
                                unfold nb068_alpha_dummy_229;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0236) 0))))
                            (show (nb068_alpha_dummy_221 f) ≠ (nb068_alpha_dummy_230 f) from (by
                                unfold nb068_alpha_dummy_230;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0237 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_218) ≠ (nb068_alpha_dummy_227) from (by
                                  unfold nb068_alpha_dummy_227;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0234) 0))))
                              (show (nb068_alpha_dummy_221 f) ≠ (nb068_alpha_dummy_228 f) from
                                (by
                                  unfold nb068_alpha_dummy_228;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0235 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_211))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_213 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_218) ≠ (nb068_alpha_dummy_229) from (by
                                unfold nb068_alpha_dummy_229;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0236) 0))))
                            (show (nb068_alpha_dummy_221 f) ≠ (nb068_alpha_dummy_230 f) from (by
                                unfold nb068_alpha_dummy_230;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0237 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_218) ≠ (nb068_alpha_dummy_227) from (by
                                  unfold nb068_alpha_dummy_227;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0234) 0))))
                              (show (nb068_alpha_dummy_221 f) ≠ (nb068_alpha_dummy_228 f) from
                                (by
                                  unfold nb068_alpha_dummy_228;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0235 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_211))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_213 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_219) ≠ (nb068_alpha_dummy_231) from (by
                                unfold nb068_alpha_dummy_231;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0240) 0))))
                            (show (nb068_alpha_dummy_222 f) ≠ (nb068_alpha_dummy_232 f) from (by
                                unfold nb068_alpha_dummy_232;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0241 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_219) ≠ (nb068_alpha_dummy_227) from (by
                                  unfold nb068_alpha_dummy_227;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0238) 0))))
                              (show (nb068_alpha_dummy_222 f) ≠ (nb068_alpha_dummy_228 f) from
                                (by
                                  unfold nb068_alpha_dummy_228;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0239 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_219) ≠ (nb068_alpha_dummy_231) from (by
                                unfold nb068_alpha_dummy_231;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0240) 0))))
                            (show (nb068_alpha_dummy_222 f) ≠ (nb068_alpha_dummy_232 f) from (by
                                unfold nb068_alpha_dummy_232;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0241 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_219) ≠ (nb068_alpha_dummy_227) from (by
                                  unfold nb068_alpha_dummy_227;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0238) 0))))
                              (show (nb068_alpha_dummy_222 f) ≠ (nb068_alpha_dummy_228 f) from
                                (by
                                  unfold nb068_alpha_dummy_228;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0239 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb068_split_alpha_0030 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_211), (nb068_alpha_dummy_213 f)),
        ((nb068_alpha_dummy_212), (nb068_alpha_dummy_214 f)),
        ((nb068_alpha_dummy_237), (nb068_alpha_dummy_238 f)),
        ((nb068_alpha_dummy_235), (nb068_alpha_dummy_236 f)),
        ((nb068_alpha_dummy_204), (nb068_alpha_dummy_206 f)),
        ((nb068_alpha_dummy_203), (nb068_alpha_dummy_205 f)),
        ((nb068_alpha_dummy_233), (nb068_alpha_dummy_234 f)),
        ((nb068_alpha_dummy_207), (nb068_alpha_dummy_208 f)),
        ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
        ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
        ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
        ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
        ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)),
        ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_211))
          (Class.cv (nb068_alpha_dummy_204))) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_212))
            (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_211)) (syn_cnnc))
              (syn_cplc (Class.cv (nb068_alpha_dummy_211)) (syn_c1c))
              (Class.cv (nb068_alpha_dummy_211))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_213 f))
          (Class.cv (nb068_alpha_dummy_206 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_214 f))
            (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_213 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb068_alpha_dummy_213 f)) (syn_c1c))
              (Class.cv (nb068_alpha_dummy_213 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068_alpha_dummy_204) ≠ (nb068_alpha_dummy_211) from (by
              unfold nb068_alpha_dummy_211;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0220) 0))))
          (show (nb068_alpha_dummy_206 f) ≠ (nb068_alpha_dummy_213 f) from (by
              unfold nb068_alpha_dummy_213;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0221 f) 0))))
          (TAlphaVar.there (show (nb068_alpha_dummy_204) ≠ (nb068_alpha_dummy_212) from (by
                unfold nb068_alpha_dummy_212;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0220) 1))))
            (show (nb068_alpha_dummy_206 f) ≠ (nb068_alpha_dummy_214 f) from (by
                unfold nb068_alpha_dummy_214;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0221 f) 1))))
            (TAlphaVar.there (show (nb068_alpha_dummy_204) ≠ (nb068_alpha_dummy_237) from (by
                  unfold nb068_alpha_dummy_237;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0250) 0))))
              (show (nb068_alpha_dummy_206 f) ≠ (nb068_alpha_dummy_238 f) from (by
                  unfold nb068_alpha_dummy_238;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0251 f) 0))))
              (TAlphaVar.there (show (nb068_alpha_dummy_204) ≠ (nb068_alpha_dummy_235) from (by
                    unfold nb068_alpha_dummy_235;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0248) 0))))
                (show (nb068_alpha_dummy_206 f) ≠ (nb068_alpha_dummy_236 f) from (by
                    unfold nb068_alpha_dummy_236;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0249 f) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_204))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_206 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068_alpha_dummy_211) ≠ (nb068_alpha_dummy_218) from (by
                                  unfold nb068_alpha_dummy_218;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0224) 1))))
                              (show (nb068_alpha_dummy_213 f) ≠ (nb068_alpha_dummy_221 f) from
                                (by
                                  unfold nb068_alpha_dummy_221;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0225 f) 1))))
                              (TAlphaVar.there
                                (show (nb068_alpha_dummy_211) ≠ (nb068_alpha_dummy_217) from (by
                                    unfold nb068_alpha_dummy_217;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0224) 0)))) (show
                                  (nb068_alpha_dummy_213 f) ≠ (nb068_alpha_dummy_220 f) from (by
                                    unfold nb068_alpha_dummy_220;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0225 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb068_alpha_dummy_211) ≠ (nb068_alpha_dummy_215) from
                                    (by
                                      unfold nb068_alpha_dummy_215;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0222)
                                              0)))) (show
                                    (nb068_alpha_dummy_213 f) ≠ (nb068_alpha_dummy_216 f) from
                                    (by
                                      unfold nb068_alpha_dummy_216;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0223 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb068_alpha_dummy_219), (nb068_alpha_dummy_222 f)),
                                  ((nb068_alpha_dummy_218), (nb068_alpha_dummy_221 f)),
                                  ((nb068_alpha_dummy_217), (nb068_alpha_dummy_220 f)),
                                  ((nb068_alpha_dummy_215), (nb068_alpha_dummy_216 f)),
                                  ((nb068_alpha_dummy_211), (nb068_alpha_dummy_213 f)),
                                  ((nb068_alpha_dummy_212), (nb068_alpha_dummy_214 f)),
                                  ((nb068_alpha_dummy_237), (nb068_alpha_dummy_238 f)),
                                  ((nb068_alpha_dummy_235), (nb068_alpha_dummy_236 f)),
                                  ((nb068_alpha_dummy_204), (nb068_alpha_dummy_206 f)),
                                  ((nb068_alpha_dummy_203), (nb068_alpha_dummy_205 f)),
                                  ((nb068_alpha_dummy_233), (nb068_alpha_dummy_234 f)),
                                  ((nb068_alpha_dummy_207), (nb068_alpha_dummy_208 f)),
                                  ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
                                  ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
                                  ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
                                  ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
                                  ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)),
                                  ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)),
                                  ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                                  ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003),
                                    (nb068_alpha_dummy_004 x y f))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb068_split_alpha_0029 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb068_alpha_dummy_211) ≠ (nb068_alpha_dummy_215) from (by
                          unfold nb068_alpha_dummy_215;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0222) 0))))
                      (show (nb068_alpha_dummy_213 f) ≠ (nb068_alpha_dummy_216 f) from (by
                          unfold nb068_alpha_dummy_216;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0223 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb068_alpha_dummy_215), (nb068_alpha_dummy_216 f)),
                      ((nb068_alpha_dummy_211), (nb068_alpha_dummy_213 f)),
                      ((nb068_alpha_dummy_212), (nb068_alpha_dummy_214 f)),
                      ((nb068_alpha_dummy_237), (nb068_alpha_dummy_238 f)),
                      ((nb068_alpha_dummy_235), (nb068_alpha_dummy_236 f)),
                      ((nb068_alpha_dummy_204), (nb068_alpha_dummy_206 f)),
                      ((nb068_alpha_dummy_203), (nb068_alpha_dummy_205 f)),
                      ((nb068_alpha_dummy_233), (nb068_alpha_dummy_234 f)),
                      ((nb068_alpha_dummy_207), (nb068_alpha_dummy_208 f)),
                      ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
                      ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
                      ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
                      ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
                      ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)),
                      ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)),
                      ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                      ((nb068_alpha_dummy_001), x),
                      ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068_alpha_dummy_211) ≠ (nb068_alpha_dummy_215) from
                      (by
                        unfold nb068_alpha_dummy_215;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0222) 0))))
                    (show (nb068_alpha_dummy_213 f) ≠ (nb068_alpha_dummy_216 f) from (by
                        unfold nb068_alpha_dummy_216;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0223 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068_alpha_dummy_211) ≠ (nb068_alpha_dummy_215) from (by
                          unfold nb068_alpha_dummy_215;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0222) 0))))
                      (show (nb068_alpha_dummy_213 f) ≠ (nb068_alpha_dummy_216 f) from (by
                          unfold nb068_alpha_dummy_216;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0223 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb068_alpha_dummy_215), (nb068_alpha_dummy_216 f)),
                      ((nb068_alpha_dummy_211), (nb068_alpha_dummy_213 f)),
                      ((nb068_alpha_dummy_212), (nb068_alpha_dummy_214 f)),
                      ((nb068_alpha_dummy_237), (nb068_alpha_dummy_238 f)),
                      ((nb068_alpha_dummy_235), (nb068_alpha_dummy_236 f)),
                      ((nb068_alpha_dummy_204), (nb068_alpha_dummy_206 f)),
                      ((nb068_alpha_dummy_203), (nb068_alpha_dummy_205 f)),
                      ((nb068_alpha_dummy_233), (nb068_alpha_dummy_234 f)),
                      ((nb068_alpha_dummy_207), (nb068_alpha_dummy_208 f)),
                      ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
                      ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
                      ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
                      ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
                      ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)),
                      ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)),
                      ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                      ((nb068_alpha_dummy_001), x),
                      ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
