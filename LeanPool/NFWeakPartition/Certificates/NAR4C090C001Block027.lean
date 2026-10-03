/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block026

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part078`. -/


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
noncomputable def nb090_split_alpha_0056 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_205 A), (nb090_alpha_dummy_206 h)),
        ((nb090_alpha_dummy_203 A), (nb090_alpha_dummy_204 h)),
        ((nb090_alpha_dummy_172 A), (nb090_alpha_dummy_174 h)),
        ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)),
        ((nb090_alpha_dummy_201 A), (nb090_alpha_dummy_202 h)),
        ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)),
        ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
        ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
        ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
        ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
        ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_205 A))
          (syn_cphi (Class.cv (nb090_alpha_dummy_172 A)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_205 A))
            (syn_cphi (Class.cv (nb090_alpha_dummy_172 A))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_206 h))
          (syn_cphi (Class.cv (nb090_alpha_dummy_174 h)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_206 h))
            (syn_cphi (Class.cv (nb090_alpha_dummy_174 h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090_alpha_dummy_172 A) ≠ (nb090_alpha_dummy_179 A) from (by
                      unfold nb090_alpha_dummy_179;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0170 A) 0))))
                  (show (nb090_alpha_dummy_174 h) ≠ (nb090_alpha_dummy_181 h) from (by
                      unfold nb090_alpha_dummy_181;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0171 h) 0))))
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_172 A) ≠ (nb090_alpha_dummy_180 A) from (by
                        unfold nb090_alpha_dummy_180;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0170 A) 1))))
                    (show (nb090_alpha_dummy_174 h) ≠ (nb090_alpha_dummy_182 h) from (by
                        unfold nb090_alpha_dummy_182;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0171 h) 1)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_172 A) ≠ (nb090_alpha_dummy_205 A) from (by
                          unfold nb090_alpha_dummy_205;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0200 A) 0))))
                      (show (nb090_alpha_dummy_174 h) ≠ (nb090_alpha_dummy_206 h) from (by
                          unfold nb090_alpha_dummy_206;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0201 h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_172 A) ≠ (nb090_alpha_dummy_203 A) from (by
                            unfold nb090_alpha_dummy_203;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0198 A) 0))))
                        (show (nb090_alpha_dummy_174 h) ≠ (nb090_alpha_dummy_204 h) from (by
                            unfold nb090_alpha_dummy_204;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0199 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_172 A))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_174 h))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_179 A) ≠ (nb090_alpha_dummy_186 A) from
                                      (by
                                        unfold nb090_alpha_dummy_186;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0174 A)
                                                1)))) (show (nb090_alpha_dummy_181 h) ≠
                                        (nb090_alpha_dummy_189 h) from (by
                                        unfold nb090_alpha_dummy_189;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0175 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb090_alpha_dummy_179 A) ≠ (nb090_alpha_dummy_185 A)
                                        from (by
                                          unfold nb090_alpha_dummy_185;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0174 A) 0)))) (show
                                        (nb090_alpha_dummy_181 h) ≠ (nb090_alpha_dummy_188 h)
                                        from (by
                                          unfold nb090_alpha_dummy_188;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0175 h) 0))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_179 A) ≠
        (nb090_alpha_dummy_183 A) from (by
          unfold nb090_alpha_dummy_183;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0172 A) 0)))) (show (nb090_alpha_dummy_181 h) ≠
        (nb090_alpha_dummy_184 h) from (by
          unfold nb090_alpha_dummy_184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0173 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_187 A),
        (nb090_alpha_dummy_190 h)), ((nb090_alpha_dummy_186 A), (nb090_alpha_dummy_189 h)),
                                        ((nb090_alpha_dummy_185 A), (nb090_alpha_dummy_188 h)),
                                        ((nb090_alpha_dummy_183 A), (nb090_alpha_dummy_184 h)),
                                        ((nb090_alpha_dummy_179 A), (nb090_alpha_dummy_181 h)),
                                        ((nb090_alpha_dummy_180 A), (nb090_alpha_dummy_182 h)),
                                        ((nb090_alpha_dummy_205 A), (nb090_alpha_dummy_206 h)),
                                        ((nb090_alpha_dummy_203 A), (nb090_alpha_dummy_204 h)),
                                        ((nb090_alpha_dummy_172 A), (nb090_alpha_dummy_174 h)),
                                        ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)),
                                        ((nb090_alpha_dummy_201 A), (nb090_alpha_dummy_202 h)),
                                        ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)),
                                        ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                                        ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                                        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                                        ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                                        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                                        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                                        ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                                        ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                                        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
                                        ((nb090_alpha_dummy_000 A), h),
                                        ((nb090_alpha_dummy_002 A), v),
                                        ((nb090_alpha_dummy_001 A), u),
                                        ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_186 A) ≠ (nb090_alpha_dummy_193 A) from (by
          unfold
            nb090_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0178
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_194 h) from (by
          unfold
            nb090_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0179
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_186 A) ≠
        (nb090_alpha_dummy_191 A) from (by
          unfold
            nb090_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0176
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_192 h) from (by
          unfold
            nb090_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0177
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_179
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_187 A) ≠
        (nb090_alpha_dummy_193 A) from (by
          unfold
            nb090_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0182
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_194 h) from (by
          unfold
            nb090_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0183
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_187 A) ≠
        (nb090_alpha_dummy_191 A) from (by
          unfold
            nb090_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0180
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_192 h) from (by
          unfold
            nb090_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0181
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_186 A) ≠ (nb090_alpha_dummy_193 A) from (by
          unfold
            nb090_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0178
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_194 h) from (by
          unfold
            nb090_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0179
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_186 A) ≠
        (nb090_alpha_dummy_191 A) from (by
          unfold
            nb090_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0176
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_192 h) from (by
          unfold
            nb090_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0177
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_179
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_187 A) ≠
        (nb090_alpha_dummy_193 A) from (by
          unfold
            nb090_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0182
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_194 h) from (by
          unfold
            nb090_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0183
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_187 A) ≠
        (nb090_alpha_dummy_191 A) from (by
          unfold
            nb090_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0180
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_192 h) from (by
          unfold
            nb090_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0181
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb090_alpha_dummy_187 A), (nb090_alpha_dummy_190 h)),
        ((nb090_alpha_dummy_186 A), (nb090_alpha_dummy_189 h)), ((nb090_alpha_dummy_185 A),
        (nb090_alpha_dummy_188 h)), ((nb090_alpha_dummy_183 A), (nb090_alpha_dummy_184 h)),
        ((nb090_alpha_dummy_179 A), (nb090_alpha_dummy_181 h)), ((nb090_alpha_dummy_180 A),
        (nb090_alpha_dummy_182 h)), ((nb090_alpha_dummy_205 A), (nb090_alpha_dummy_206 h)),
        ((nb090_alpha_dummy_203 A), (nb090_alpha_dummy_204 h)), ((nb090_alpha_dummy_172 A),
        (nb090_alpha_dummy_174 h)), ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)),
        ((nb090_alpha_dummy_201 A), (nb090_alpha_dummy_202 h)), ((nb090_alpha_dummy_175 A),
        (nb090_alpha_dummy_176 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
        ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A),
        (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A),
        (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
        ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A),
        (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                                        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_186 A) ≠ (nb090_alpha_dummy_197 A) from (by
          unfold
            nb090_alpha_dummy_197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0186
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_198 h) from (by
          unfold
            nb090_alpha_dummy_198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0187
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_186 A) ≠
        (nb090_alpha_dummy_195 A) from (by
          unfold
            nb090_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0184
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_196 h) from (by
          unfold
            nb090_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0185
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_179
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_186 A) ≠
        (nb090_alpha_dummy_197 A) from (by
          unfold
            nb090_alpha_dummy_197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0186
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_198 h) from (by
          unfold
            nb090_alpha_dummy_198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0187
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_186 A) ≠
        (nb090_alpha_dummy_195 A) from (by
          unfold
            nb090_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0184
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_196 h) from (by
          unfold
            nb090_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0185
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_179
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_187 A) ≠ (nb090_alpha_dummy_199 A) from (by
          unfold
            nb090_alpha_dummy_199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0190
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_200 h) from (by
          unfold
            nb090_alpha_dummy_200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0191
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_187 A) ≠
        (nb090_alpha_dummy_195 A) from (by
          unfold
            nb090_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0188
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_196 h) from (by
          unfold
            nb090_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0189
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_187 A) ≠ (nb090_alpha_dummy_199 A) from (by
          unfold
            nb090_alpha_dummy_199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0190
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_200 h) from (by
          unfold
            nb090_alpha_dummy_200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0191
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_187 A) ≠
        (nb090_alpha_dummy_195 A) from (by
          unfold
            nb090_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0188
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_196 h) from (by
          unfold
            nb090_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0189
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_179 A) ≠ (nb090_alpha_dummy_183 A) from (by
                                unfold nb090_alpha_dummy_183;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0172 A) 0))))
                            (show (nb090_alpha_dummy_181 h) ≠ (nb090_alpha_dummy_184 h) from (by
                                unfold nb090_alpha_dummy_184;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0173 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb090_alpha_dummy_183 A), (nb090_alpha_dummy_184 h)),
                            ((nb090_alpha_dummy_179 A), (nb090_alpha_dummy_181 h)),
                            ((nb090_alpha_dummy_180 A), (nb090_alpha_dummy_182 h)),
                            ((nb090_alpha_dummy_205 A), (nb090_alpha_dummy_206 h)),
                            ((nb090_alpha_dummy_203 A), (nb090_alpha_dummy_204 h)),
                            ((nb090_alpha_dummy_172 A), (nb090_alpha_dummy_174 h)),
                            ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)),
                            ((nb090_alpha_dummy_201 A), (nb090_alpha_dummy_202 h)),
                            ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)),
                            ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                            ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                            ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                            ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                            ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                            ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                            ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                            ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                            ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
                            ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                            ((nb090_alpha_dummy_001 A), u),
                            ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_179 A) ≠ (nb090_alpha_dummy_183 A) from (by
                              unfold nb090_alpha_dummy_183;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0172 A) 0))))
                          (show (nb090_alpha_dummy_181 h) ≠ (nb090_alpha_dummy_184 h) from (by
                              unfold nb090_alpha_dummy_184;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0173 h) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_179 A) ≠ (nb090_alpha_dummy_183 A) from (by
                                unfold nb090_alpha_dummy_183;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0172 A) 0))))
                            (show (nb090_alpha_dummy_181 h) ≠ (nb090_alpha_dummy_184 h) from (by
                                unfold nb090_alpha_dummy_184;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0173 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb090_alpha_dummy_183 A), (nb090_alpha_dummy_184 h)),
                            ((nb090_alpha_dummy_179 A), (nb090_alpha_dummy_181 h)),
                            ((nb090_alpha_dummy_180 A), (nb090_alpha_dummy_182 h)),
                            ((nb090_alpha_dummy_205 A), (nb090_alpha_dummy_206 h)),
                            ((nb090_alpha_dummy_203 A), (nb090_alpha_dummy_204 h)),
                            ((nb090_alpha_dummy_172 A), (nb090_alpha_dummy_174 h)),
                            ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)),
                            ((nb090_alpha_dummy_201 A), (nb090_alpha_dummy_202 h)),
                            ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)),
                            ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                            ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                            ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                            ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                            ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                            ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                            ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                            ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                            ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
                            ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                            ((nb090_alpha_dummy_001 A), u),
                            ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb090_alpha_dummy_172 A) ≠ (nb090_alpha_dummy_179 A) from (by
                        unfold nb090_alpha_dummy_179;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0170 A) 0))))
                    (show (nb090_alpha_dummy_174 h) ≠ (nb090_alpha_dummy_181 h) from (by
                        unfold nb090_alpha_dummy_181;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0171 h) 0)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_172 A) ≠ (nb090_alpha_dummy_180 A) from (by
                          unfold nb090_alpha_dummy_180;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0170 A) 1))))
                      (show (nb090_alpha_dummy_174 h) ≠ (nb090_alpha_dummy_182 h) from (by
                          unfold nb090_alpha_dummy_182;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0171 h) 1))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_172 A) ≠ (nb090_alpha_dummy_205 A) from (by
                            unfold nb090_alpha_dummy_205;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0200 A) 0))))
                        (show (nb090_alpha_dummy_174 h) ≠ (nb090_alpha_dummy_206 h) from (by
                            unfold nb090_alpha_dummy_206;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0201 h) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_172 A) ≠ (nb090_alpha_dummy_203 A) from (by
                              unfold nb090_alpha_dummy_203;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0198 A) 0))))
                          (show (nb090_alpha_dummy_174 h) ≠ (nb090_alpha_dummy_204 h) from (by
                              unfold nb090_alpha_dummy_204;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0199 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_172 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_174 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb090_alpha_dummy_179 A) ≠
        (nb090_alpha_dummy_186 A) from (by
                                          unfold nb090_alpha_dummy_186;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0174 A) 1)))) (show
                                        (nb090_alpha_dummy_181 h) ≠ (nb090_alpha_dummy_189 h)
                                        from (by
                                          unfold nb090_alpha_dummy_189;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0175 h) 1))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_179 A) ≠
        (nb090_alpha_dummy_185 A) from (by
          unfold nb090_alpha_dummy_185;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0174 A) 0)))) (show (nb090_alpha_dummy_181 h) ≠
        (nb090_alpha_dummy_188 h) from (by
          unfold nb090_alpha_dummy_188;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0175 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_179 A) ≠ (nb090_alpha_dummy_183 A) from (by
          unfold nb090_alpha_dummy_183;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0172 A) 0)))) (show (nb090_alpha_dummy_181 h) ≠
        (nb090_alpha_dummy_184 h) from (by
          unfold nb090_alpha_dummy_184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0173 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_187 A),
        (nb090_alpha_dummy_190 h)), ((nb090_alpha_dummy_186 A), (nb090_alpha_dummy_189 h)),
        ((nb090_alpha_dummy_185 A), (nb090_alpha_dummy_188 h)), ((nb090_alpha_dummy_183 A),
        (nb090_alpha_dummy_184 h)), ((nb090_alpha_dummy_179 A), (nb090_alpha_dummy_181 h)),
        ((nb090_alpha_dummy_180 A), (nb090_alpha_dummy_182 h)), ((nb090_alpha_dummy_205 A),
        (nb090_alpha_dummy_206 h)), ((nb090_alpha_dummy_203 A), (nb090_alpha_dummy_204 h)),
        ((nb090_alpha_dummy_172 A), (nb090_alpha_dummy_174 h)), ((nb090_alpha_dummy_171 A),
        (nb090_alpha_dummy_173 h)), ((nb090_alpha_dummy_201 A), (nb090_alpha_dummy_202 h)),
        ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)), ((nb090_alpha_dummy_130 A),
        (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_425 A),
        (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A),
        (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                                        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_186 A) ≠ (nb090_alpha_dummy_193 A) from (by
          unfold
            nb090_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0178
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_194 h) from (by
          unfold
            nb090_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0179
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_186 A) ≠
        (nb090_alpha_dummy_191 A) from (by
          unfold
            nb090_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0176
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_192 h) from (by
          unfold
            nb090_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0177
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_179
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_187 A) ≠ (nb090_alpha_dummy_193 A) from (by
          unfold
            nb090_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0182
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_194 h) from (by
          unfold
            nb090_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0183
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_187 A) ≠
        (nb090_alpha_dummy_191 A) from (by
          unfold
            nb090_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0180
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_192 h) from (by
          unfold
            nb090_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0181
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_186 A) ≠ (nb090_alpha_dummy_193 A) from (by
          unfold
            nb090_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0178
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_194 h) from (by
          unfold
            nb090_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0179
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_186 A) ≠
        (nb090_alpha_dummy_191 A) from (by
          unfold
            nb090_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0176
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_192 h) from (by
          unfold
            nb090_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0177
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_179
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_187 A) ≠ (nb090_alpha_dummy_193 A) from (by
          unfold
            nb090_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0182
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_194 h) from (by
          unfold
            nb090_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0183
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_187 A) ≠
        (nb090_alpha_dummy_191 A) from (by
          unfold
            nb090_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0180
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_192 h) from (by
          unfold
            nb090_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0181
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_187 A), (nb090_alpha_dummy_190 h)), ((nb090_alpha_dummy_186 A),
        (nb090_alpha_dummy_189 h)), ((nb090_alpha_dummy_185 A), (nb090_alpha_dummy_188 h)),
        ((nb090_alpha_dummy_183 A), (nb090_alpha_dummy_184 h)), ((nb090_alpha_dummy_179 A),
        (nb090_alpha_dummy_181 h)), ((nb090_alpha_dummy_180 A), (nb090_alpha_dummy_182 h)),
        ((nb090_alpha_dummy_205 A), (nb090_alpha_dummy_206 h)), ((nb090_alpha_dummy_203 A),
        (nb090_alpha_dummy_204 h)), ((nb090_alpha_dummy_172 A), (nb090_alpha_dummy_174 h)),
        ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)), ((nb090_alpha_dummy_201 A),
        (nb090_alpha_dummy_202 h)), ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)),
        ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A),
        (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
        ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A),
        (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
        ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A),
        (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c0) (by simp only [fv_syn_c0])))
                                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_186 A) ≠ (nb090_alpha_dummy_197 A) from (by
          unfold
            nb090_alpha_dummy_197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0186
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_198 h) from (by
          unfold
            nb090_alpha_dummy_198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0187
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_186 A) ≠
        (nb090_alpha_dummy_195 A) from (by
          unfold
            nb090_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0184
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_196 h) from (by
          unfold
            nb090_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0185
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_179
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_186 A) ≠ (nb090_alpha_dummy_197 A) from (by
          unfold
            nb090_alpha_dummy_197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0186
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_198 h) from (by
          unfold
            nb090_alpha_dummy_198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0187
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_186 A) ≠
        (nb090_alpha_dummy_195 A) from (by
          unfold
            nb090_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0184
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_196 h) from (by
          unfold
            nb090_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0185
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_179
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_187 A) ≠ (nb090_alpha_dummy_199 A) from (by
          unfold
            nb090_alpha_dummy_199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0190
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_200 h) from (by
          unfold
            nb090_alpha_dummy_200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0191
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_187 A) ≠
        (nb090_alpha_dummy_195 A) from (by
          unfold
            nb090_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0188
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_196 h) from (by
          unfold
            nb090_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0189
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_187 A) ≠ (nb090_alpha_dummy_199 A) from (by
          unfold
            nb090_alpha_dummy_199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0190
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_200 h) from (by
          unfold
            nb090_alpha_dummy_200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0191
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_187 A) ≠
        (nb090_alpha_dummy_195 A) from (by
          unfold
            nb090_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0188
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_196 h) from (by
          unfold
            nb090_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0189
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090_alpha_dummy_179 A) ≠ (nb090_alpha_dummy_183 A) from
                                (by
                                  unfold nb090_alpha_dummy_183;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0172 A) 0))))
                              (show (nb090_alpha_dummy_181 h) ≠ (nb090_alpha_dummy_184 h) from
                                (by
                                  unfold nb090_alpha_dummy_184;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0173 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb090_alpha_dummy_183 A), (nb090_alpha_dummy_184 h)),
                              ((nb090_alpha_dummy_179 A), (nb090_alpha_dummy_181 h)),
                              ((nb090_alpha_dummy_180 A), (nb090_alpha_dummy_182 h)),
                              ((nb090_alpha_dummy_205 A), (nb090_alpha_dummy_206 h)),
                              ((nb090_alpha_dummy_203 A), (nb090_alpha_dummy_204 h)),
                              ((nb090_alpha_dummy_172 A), (nb090_alpha_dummy_174 h)),
                              ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)),
                              ((nb090_alpha_dummy_201 A), (nb090_alpha_dummy_202 h)),
                              ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)),
                              ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                              ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                              ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                              ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                              ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                              ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                              ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                              ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                              ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
                              ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                              ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                (nb090_alpha_dummy_004 v u A h))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_179 A) ≠ (nb090_alpha_dummy_183 A) from (by
                                unfold nb090_alpha_dummy_183;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0172 A) 0))))
                            (show (nb090_alpha_dummy_181 h) ≠ (nb090_alpha_dummy_184 h) from (by
                                unfold nb090_alpha_dummy_184;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0173 h) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090_alpha_dummy_179 A) ≠ (nb090_alpha_dummy_183 A) from
                                (by
                                  unfold nb090_alpha_dummy_183;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0172 A) 0))))
                              (show (nb090_alpha_dummy_181 h) ≠ (nb090_alpha_dummy_184 h) from
                                (by
                                  unfold nb090_alpha_dummy_184;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0173 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb090_alpha_dummy_183 A), (nb090_alpha_dummy_184 h)),
                              ((nb090_alpha_dummy_179 A), (nb090_alpha_dummy_181 h)),
                              ((nb090_alpha_dummy_180 A), (nb090_alpha_dummy_182 h)),
                              ((nb090_alpha_dummy_205 A), (nb090_alpha_dummy_206 h)),
                              ((nb090_alpha_dummy_203 A), (nb090_alpha_dummy_204 h)),
                              ((nb090_alpha_dummy_172 A), (nb090_alpha_dummy_174 h)),
                              ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)),
                              ((nb090_alpha_dummy_201 A), (nb090_alpha_dummy_202 h)),
                              ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)),
                              ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                              ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                              ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                              ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                              ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                              ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                              ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                              ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                              ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
                              ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                              ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                (nb090_alpha_dummy_004 v u A h))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part079`. -/


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
noncomputable def nb090_split_alpha_0057 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
        ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
        ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classEq (Class.cv (nb090_alpha_dummy_429 A))
          (syn_cop (Class.cv (nb090_alpha_dummy_423 A)) (Class.cv (nb090_alpha_dummy_424 A))))
        (Wff.neg (syn_wex (nb090_alpha_dummy_425 A) (syn_wa
              (syn_wbr (Class.cv (nb090_alpha_dummy_423 A))
                (syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))
                (Class.cv (nb090_alpha_dummy_425 A)))
              (syn_wbr (Class.cv (nb090_alpha_dummy_425 A))
                (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))
                (Class.cv (nb090_alpha_dummy_424 A)))))))
      (Wff.imp (Wff.classEq (Class.cv (nb090_alpha_dummy_430 h))
          (syn_cop (Class.cv (nb090_alpha_dummy_426 h)) (Class.cv (nb090_alpha_dummy_427 h))))
        (Wff.neg (syn_wex (nb090_alpha_dummy_428 h) (syn_wa
              (syn_wbr (Class.cv (nb090_alpha_dummy_426 h))
                (syn_ccnv (syn_ccnv (Class.cv h))) (Class.cv (nb090_alpha_dummy_428 h)))
              (syn_wbr (Class.cv (nb090_alpha_dummy_428 h)) (syn_ccnv (Class.cv h))
                (Class.cv (nb090_alpha_dummy_427 h))))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
            (show (nb090_alpha_dummy_424 A) ≠ (nb090_alpha_dummy_429 A) from (by
                unfold nb090_alpha_dummy_429;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0434 A) 0)))))
          (Ne.symm (show (nb090_alpha_dummy_427 h) ≠ (nb090_alpha_dummy_430 h) from (by
                unfold nb090_alpha_dummy_430;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0435 h) 0)))))
          (TAlphaVar.there (Ne.symm
              (show (nb090_alpha_dummy_423 A) ≠ (nb090_alpha_dummy_429 A) from (by
                  unfold nb090_alpha_dummy_429;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0432 A) 0)))))
            (Ne.symm (show (nb090_alpha_dummy_426 h) ≠ (nb090_alpha_dummy_430 h) from (by
                  unfold nb090_alpha_dummy_430;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0433 h) 0)))))
            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0038 v u A h)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_424 A) ≠ (nb090_alpha_dummy_432 A) from
                                    (by
                                      unfold nb090_alpha_dummy_432;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0464 A)
                                              1)))) (show
                                    (nb090_alpha_dummy_427 h) ≠ (nb090_alpha_dummy_434 h) from
                                    (by
                                      unfold nb090_alpha_dummy_434;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0466 h)
                                              1)))) (TAlphaVar.there (show
                                      (nb090_alpha_dummy_424 A) ≠ (nb090_alpha_dummy_431 A) from
                                      (by
                                        unfold nb090_alpha_dummy_431;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0464 A)
                                                0)))) (show (nb090_alpha_dummy_427 h) ≠
                                        (nb090_alpha_dummy_433 h) from (by
                                        unfold nb090_alpha_dummy_433;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0466 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb090_alpha_dummy_424 A) ≠ (nb090_alpha_dummy_461 A)
                                        from (by
                                          unfold nb090_alpha_dummy_461;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0468 A) 0)))) (show
                                        (nb090_alpha_dummy_427 h) ≠ (nb090_alpha_dummy_462 h)
                                        from (by
                                          unfold nb090_alpha_dummy_462;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0469 h) 0))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_424 A) ≠
        (nb090_alpha_dummy_435 A) from (by
          unfold nb090_alpha_dummy_435;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0465 A) 0)))) (show (nb090_alpha_dummy_427 h) ≠
        (nb090_alpha_dummy_436 h) from (by
          unfold nb090_alpha_dummy_436;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0467 h) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪
                                      ((Class.cv (nb090_alpha_dummy_424 A))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪
                                      ((Class.cv (nb090_alpha_dummy_427 h))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (nb090_split_alpha_0039 v u A h)
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_463 A),
        (nb090_alpha_dummy_464 h)), ((nb090_alpha_dummy_432 A), (nb090_alpha_dummy_434 h)),
        ((nb090_alpha_dummy_431 A), (nb090_alpha_dummy_433 h)), ((nb090_alpha_dummy_461 A),
        (nb090_alpha_dummy_462 h)), ((nb090_alpha_dummy_435 A), (nb090_alpha_dummy_436 h)),
        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A),
        (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
        ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A),
        (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                                        (syn_ccompl (syn_csn (syn_c0c))) (by
                                          simp only [fv_syn_ccompl, fv_syn_csn,
                                            fv_syn_c0c])))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_424 A) ≠ (nb090_alpha_dummy_432 A) from
                                    (by
                                      unfold nb090_alpha_dummy_432;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0464 A)
                                              1)))) (show
                                    (nb090_alpha_dummy_427 h) ≠ (nb090_alpha_dummy_434 h) from
                                    (by
                                      unfold nb090_alpha_dummy_434;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0466 h)
                                              1)))) (TAlphaVar.there (show
                                      (nb090_alpha_dummy_424 A) ≠ (nb090_alpha_dummy_431 A) from
                                      (by
                                        unfold nb090_alpha_dummy_431;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0464 A)
                                                0)))) (show (nb090_alpha_dummy_427 h) ≠
                                        (nb090_alpha_dummy_433 h) from (by
                                        unfold nb090_alpha_dummy_433;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0466 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb090_alpha_dummy_424 A) ≠ (nb090_alpha_dummy_461 A)
                                        from (by
                                          unfold nb090_alpha_dummy_461;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0468 A) 0)))) (show
                                        (nb090_alpha_dummy_427 h) ≠ (nb090_alpha_dummy_462 h)
                                        from (by
                                          unfold nb090_alpha_dummy_462;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0469 h) 0))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_424 A) ≠
        (nb090_alpha_dummy_435 A) from (by
          unfold nb090_alpha_dummy_435;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0465 A) 0)))) (show (nb090_alpha_dummy_427 h) ≠
        (nb090_alpha_dummy_436 h) from (by
          unfold nb090_alpha_dummy_436;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0467 h) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪
                                      ((Class.cv (nb090_alpha_dummy_424 A))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪
                                      ((Class.cv (nb090_alpha_dummy_427 h))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (nb090_split_alpha_0039 v u A h)
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_463 A),
        (nb090_alpha_dummy_464 h)), ((nb090_alpha_dummy_432 A), (nb090_alpha_dummy_434 h)),
        ((nb090_alpha_dummy_431 A), (nb090_alpha_dummy_433 h)), ((nb090_alpha_dummy_461 A),
        (nb090_alpha_dummy_462 h)), ((nb090_alpha_dummy_435 A), (nb090_alpha_dummy_436 h)),
        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A),
        (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
        ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A),
        (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                                        (syn_ccompl (syn_csn (syn_c0c))) (by
                                          simp only [fv_syn_ccompl, fv_syn_csn,
                                            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0040 v u A h)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb090_alpha_dummy_425 A) ≠
        (nb090_alpha_dummy_468 A) from (by
          unfold nb090_alpha_dummy_468;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0502 A) 1)))) (show (nb090_alpha_dummy_428 h) ≠
        (nb090_alpha_dummy_470 h) from (by
          unfold nb090_alpha_dummy_470;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0504 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_425 A) ≠ (nb090_alpha_dummy_467 A) from (by
          unfold nb090_alpha_dummy_467;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0502 A) 0)))) (show (nb090_alpha_dummy_428 h) ≠
        (nb090_alpha_dummy_469 h) from (by
          unfold nb090_alpha_dummy_469;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0504 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_425 A) ≠ (nb090_alpha_dummy_497 A) from (by
          unfold nb090_alpha_dummy_497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0506 A) 0)))) (show (nb090_alpha_dummy_428 h) ≠
        (nb090_alpha_dummy_498 h) from (by
          unfold nb090_alpha_dummy_498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0507 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_425 A) ≠ (nb090_alpha_dummy_471 A) from (by
          unfold nb090_alpha_dummy_471;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0503 A) 0)))) (show (nb090_alpha_dummy_428 h) ≠
        (nb090_alpha_dummy_472 h) from (by
          unfold nb090_alpha_dummy_472;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0505 h) 0)))) (TAlphaVar.here _ _ _)))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_425 A))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_428 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0041 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_499 A), (nb090_alpha_dummy_500 h)), ((nb090_alpha_dummy_468 A),
        (nb090_alpha_dummy_470 h)), ((nb090_alpha_dummy_467 A), (nb090_alpha_dummy_469 h)),
        ((nb090_alpha_dummy_497 A), (nb090_alpha_dummy_498 h)), ((nb090_alpha_dummy_471 A),
        (nb090_alpha_dummy_472 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A),
        (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
        ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A),
        (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb090_alpha_dummy_425 A) ≠
        (nb090_alpha_dummy_468 A) from (by
          unfold nb090_alpha_dummy_468;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0502 A) 1)))) (show (nb090_alpha_dummy_428 h) ≠
        (nb090_alpha_dummy_470 h) from (by
          unfold nb090_alpha_dummy_470;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0504 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_425 A) ≠ (nb090_alpha_dummy_467 A) from (by
          unfold nb090_alpha_dummy_467;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0502 A) 0)))) (show (nb090_alpha_dummy_428 h) ≠
        (nb090_alpha_dummy_469 h) from (by
          unfold nb090_alpha_dummy_469;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0504 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_425 A) ≠ (nb090_alpha_dummy_497 A) from (by
          unfold nb090_alpha_dummy_497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0506 A) 0)))) (show (nb090_alpha_dummy_428 h) ≠
        (nb090_alpha_dummy_498 h) from (by
          unfold nb090_alpha_dummy_498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0507 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_425 A) ≠ (nb090_alpha_dummy_471 A) from (by
          unfold nb090_alpha_dummy_471;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0503 A) 0)))) (show (nb090_alpha_dummy_428 h) ≠
        (nb090_alpha_dummy_472 h) from (by
          unfold nb090_alpha_dummy_472;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0505 h) 0)))) (TAlphaVar.here _ _ _)))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_425 A))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_428 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0041 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_499 A), (nb090_alpha_dummy_500 h)), ((nb090_alpha_dummy_468 A),
        (nb090_alpha_dummy_470 h)), ((nb090_alpha_dummy_467 A), (nb090_alpha_dummy_469 h)),
        ((nb090_alpha_dummy_497 A), (nb090_alpha_dummy_498 h)), ((nb090_alpha_dummy_471 A),
        (nb090_alpha_dummy_472 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A),
        (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
        ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A),
        (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cab (TAlphaWff.ex
                (TAlphaWff.ex (TAlphaWff.neg (nb090_split_alpha_0050 v u A h))))))
          (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0051 v u A h)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb090_alpha_dummy_424 A) ≠
        (nb090_alpha_dummy_582 A) from (by
          unfold nb090_alpha_dummy_582;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0632 A) 1)))) (show (nb090_alpha_dummy_427 h) ≠
        (nb090_alpha_dummy_584 h) from (by
          unfold nb090_alpha_dummy_584;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0634 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_424 A) ≠ (nb090_alpha_dummy_581 A) from (by
          unfold nb090_alpha_dummy_581;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0632 A) 0)))) (show (nb090_alpha_dummy_427 h) ≠
        (nb090_alpha_dummy_583 h) from (by
          unfold nb090_alpha_dummy_583;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0634 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_424 A) ≠ (nb090_alpha_dummy_611 A) from (by
          unfold nb090_alpha_dummy_611;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0636 A) 0)))) (show (nb090_alpha_dummy_427 h) ≠
        (nb090_alpha_dummy_612 h) from (by
          unfold nb090_alpha_dummy_612;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0637 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_424 A) ≠ (nb090_alpha_dummy_585 A) from (by
          unfold nb090_alpha_dummy_585;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0633 A) 0)))) (show (nb090_alpha_dummy_427 h) ≠
        (nb090_alpha_dummy_586 h) from (by
          unfold nb090_alpha_dummy_586;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0635 h) 0)))) (TAlphaVar.there (freshVar_injective
        (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv
        (nb090_alpha_dummy_000 A))))).fv) (by decide)) (freshVar_injective
        (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_425 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_424 A))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_428 h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_427 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0052 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_613 A), (nb090_alpha_dummy_614 h)), ((nb090_alpha_dummy_582 A),
        (nb090_alpha_dummy_584 h)), ((nb090_alpha_dummy_581 A), (nb090_alpha_dummy_583 h)),
        ((nb090_alpha_dummy_611 A), (nb090_alpha_dummy_612 h)), ((nb090_alpha_dummy_585 A),
        (nb090_alpha_dummy_586 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A),
        (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
        ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A),
        (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb090_alpha_dummy_424 A) ≠
        (nb090_alpha_dummy_582 A) from (by
          unfold nb090_alpha_dummy_582;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0632 A) 1)))) (show (nb090_alpha_dummy_427 h) ≠
        (nb090_alpha_dummy_584 h) from (by
          unfold nb090_alpha_dummy_584;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0634 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_424 A) ≠ (nb090_alpha_dummy_581 A) from (by
          unfold nb090_alpha_dummy_581;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0632 A) 0)))) (show (nb090_alpha_dummy_427 h) ≠
        (nb090_alpha_dummy_583 h) from (by
          unfold nb090_alpha_dummy_583;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0634 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_424 A) ≠ (nb090_alpha_dummy_611 A) from (by
          unfold nb090_alpha_dummy_611;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0636 A) 0)))) (show (nb090_alpha_dummy_427 h) ≠
        (nb090_alpha_dummy_612 h) from (by
          unfold nb090_alpha_dummy_612;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0637 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_424 A) ≠ (nb090_alpha_dummy_585 A) from (by
          unfold nb090_alpha_dummy_585;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0633 A) 0)))) (show (nb090_alpha_dummy_427 h) ≠
        (nb090_alpha_dummy_586 h) from (by
          unfold nb090_alpha_dummy_586;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0635 h) 0)))) (TAlphaVar.there (freshVar_injective
        (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv
        (nb090_alpha_dummy_000 A))))).fv) (by decide)) (freshVar_injective
        (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_425 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_424 A))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_428 h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_427 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0052 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_613 A), (nb090_alpha_dummy_614 h)), ((nb090_alpha_dummy_582 A),
        (nb090_alpha_dummy_584 h)), ((nb090_alpha_dummy_581 A), (nb090_alpha_dummy_583 h)),
        ((nb090_alpha_dummy_611 A), (nb090_alpha_dummy_612 h)), ((nb090_alpha_dummy_585 A),
        (nb090_alpha_dummy_586 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A),
        (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
        ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A),
        (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
                  (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
                            (show (nb090_alpha_dummy_130 A) ≠ (nb090_alpha_dummy_133 A) from (by
                                unfold nb090_alpha_dummy_133;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0124 A) 0)))))
                          (Ne.symm (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_134 h)
                              from (by
                                unfold nb090_alpha_dummy_134;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0125 h) 0)))))
                          (TAlphaVar.there (Ne.symm
                              (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_133 A) from
                                (by
                                  unfold nb090_alpha_dummy_133;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0122 A) 0)))))
                            (Ne.symm (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_134 h)
                                from (by
                                  unfold nb090_alpha_dummy_134;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0123 h) 0)))))
                            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb090_split_alpha_0053 v u A h)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_130 A) ≠ (nb090_alpha_dummy_136 A) from (by
          unfold nb090_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0154 A)
                  1)))) (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_138 h) from (by
          unfold nb090_alpha_dummy_138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0156 h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_130 A) ≠
        (nb090_alpha_dummy_135 A) from (by
          unfold nb090_alpha_dummy_135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0154 A)
                  0)))) (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_137 h) from (by
          unfold nb090_alpha_dummy_137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0156 h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_130 A) ≠
        (nb090_alpha_dummy_165 A) from (by
          unfold nb090_alpha_dummy_165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0158
                    A)
                  0)))) (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_166 h) from (by
          unfold nb090_alpha_dummy_166;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0159
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_130 A) ≠
        (nb090_alpha_dummy_139 A) from (by
          unfold nb090_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0155
                    A)
                  0)))) (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_140 h) from (by
          unfold nb090_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0157
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_129 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_130 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_131 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_132 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0054 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)), ((nb090_alpha_dummy_136 A),
        (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
        ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)), ((nb090_alpha_dummy_139 A),
        (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
        ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A),
        (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A),
        (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
        ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A),
        (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_130 A) ≠ (nb090_alpha_dummy_136 A) from (by
          unfold nb090_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0154 A)
                  1)))) (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_138 h) from (by
          unfold nb090_alpha_dummy_138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0156 h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_130 A) ≠
        (nb090_alpha_dummy_135 A) from (by
          unfold nb090_alpha_dummy_135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0154 A)
                  0)))) (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_137 h) from (by
          unfold nb090_alpha_dummy_137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0156 h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_130 A) ≠
        (nb090_alpha_dummy_165 A) from (by
          unfold nb090_alpha_dummy_165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0158
                    A)
                  0)))) (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_166 h) from (by
          unfold nb090_alpha_dummy_166;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0159
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_130 A) ≠
        (nb090_alpha_dummy_139 A) from (by
          unfold nb090_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0155
                    A)
                  0)))) (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_140 h) from (by
          unfold nb090_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0157
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_129 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_130 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_131 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_132 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0054 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)), ((nb090_alpha_dummy_136 A),
        (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
        ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)), ((nb090_alpha_dummy_139 A),
        (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
        ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A),
        (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A),
        (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
        ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A),
        (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb090_split_alpha_0055 v u A h)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_172 A) from (by
          unfold nb090_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0192 A)
                  1)))) (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_174 h) from (by
          unfold nb090_alpha_dummy_174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0194 h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_129 A) ≠
        (nb090_alpha_dummy_171 A) from (by
          unfold nb090_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0192 A)
                  0)))) (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_173 h) from (by
          unfold nb090_alpha_dummy_173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0194 h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_129 A) ≠
        (nb090_alpha_dummy_201 A) from (by
          unfold nb090_alpha_dummy_201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0196
                    A)
                  0)))) (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_202 h) from (by
          unfold nb090_alpha_dummy_202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0197
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_129 A) ≠
        (nb090_alpha_dummy_175 A) from (by
          unfold nb090_alpha_dummy_175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0193
                    A)
                  0)))) (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_176 h) from (by
          unfold nb090_alpha_dummy_176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0195
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_000
        A))).fv) (by decide)) (freshVar_injective (((Class.cv h)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_130 A))).fv ∪ ((Class.cv
        (nb090_alpha_dummy_129 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_132 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_131 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0056 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_203 A), (nb090_alpha_dummy_204 h)), ((nb090_alpha_dummy_172 A),
        (nb090_alpha_dummy_174 h)), ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)),
        ((nb090_alpha_dummy_201 A), (nb090_alpha_dummy_202 h)), ((nb090_alpha_dummy_175 A),
        (nb090_alpha_dummy_176 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
        ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A),
        (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A),
        (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
        ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A),
        (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_172 A) from (by
          unfold nb090_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0192 A)
                  1)))) (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_174 h) from (by
          unfold nb090_alpha_dummy_174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0194 h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_129 A) ≠
        (nb090_alpha_dummy_171 A) from (by
          unfold nb090_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0192 A)
                  0)))) (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_173 h) from (by
          unfold nb090_alpha_dummy_173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0194 h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_129 A) ≠
        (nb090_alpha_dummy_201 A) from (by
          unfold nb090_alpha_dummy_201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0196
                    A)
                  0)))) (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_202 h) from (by
          unfold nb090_alpha_dummy_202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0197
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_129 A) ≠
        (nb090_alpha_dummy_175 A) from (by
          unfold nb090_alpha_dummy_175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0193
                    A)
                  0)))) (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_176 h) from (by
          unfold nb090_alpha_dummy_176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0195
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_000
        A))).fv) (by decide)) (freshVar_injective (((Class.cv h)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_130 A))).fv ∪ ((Class.cv
        (nb090_alpha_dummy_129 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_132 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_131 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0056 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_203 A), (nb090_alpha_dummy_204 h)), ((nb090_alpha_dummy_172 A),
        (nb090_alpha_dummy_174 h)), ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)),
        ((nb090_alpha_dummy_201 A), (nb090_alpha_dummy_202 h)), ((nb090_alpha_dummy_175 A),
        (nb090_alpha_dummy_176 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
        ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A),
        (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A),
        (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
        ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A),
        (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there
                          (show (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_130 A) from (by
                              unfold nb090_alpha_dummy_130;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0212 A) 1))))
                          (show h ≠ (nb090_alpha_dummy_132 h) from (by
                              unfold nb090_alpha_dummy_132;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0213 h) 1))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_129 A) from (by
                                unfold nb090_alpha_dummy_129;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0212 A) 0))))
                            (show h ≠ (nb090_alpha_dummy_131 h) from (by
                                unfold nb090_alpha_dummy_131;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0213 h) 0))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_133 A) from
                                (by
                                  unfold nb090_alpha_dummy_133;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0210 A) 0))))
                              (show h ≠ (nb090_alpha_dummy_134 h) from (by
                                  unfold nb090_alpha_dummy_134;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0211 h) 0))))
                              (TAlphaVar.there (show
                                  (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_425 A) from (by
                                    unfold nb090_alpha_dummy_425;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0596 A)
                                            2)))) (show h ≠ (nb090_alpha_dummy_428 h) from (by
                                    unfold nb090_alpha_dummy_428;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0598 h)
                                            2)))) (TAlphaVar.there (show
                                    (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_424 A) from
                                    (by
                                      unfold nb090_alpha_dummy_424;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0596 A)
                                              1)))) (show h ≠ (nb090_alpha_dummy_427 h) from (by
                                      unfold nb090_alpha_dummy_427;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0598 h)
                                              1)))) (TAlphaVar.there (show
                                      (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_423 A) from
                                      (by
                                        unfold nb090_alpha_dummy_423;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0596 A)
                                                0)))) (show h ≠ (nb090_alpha_dummy_426 h) from
                                      (by
                                        unfold nb090_alpha_dummy_426;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0598 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_429 A)
                                        from (by
                                          unfold nb090_alpha_dummy_429;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0597 A) 0))))
                                      (show h ≠ (nb090_alpha_dummy_430 h) from (by
                                          unfold nb090_alpha_dummy_430;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0599 h) 0))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_421 A) from (by
          unfold nb090_alpha_dummy_421;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0594 A) 0)))) (show h ≠ (nb090_alpha_dummy_422 h) from (by
          unfold nb090_alpha_dummy_422;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0595 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_419 A) from (by
          unfold nb090_alpha_dummy_419;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0592 A) 0)))) (show h ≠ (nb090_alpha_dummy_420 h) from (by
          unfold nb090_alpha_dummy_420;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0593 h) 0)))) (TAlphaVar.here _ _ _)))))))))))))))))))))

theorem nb090_wpp_notmem_1584 (A : Class) : (nb090_alpha_dummy_421 A) ∉ ((syn_cid)).fv :=
  by simpa only [nb090_alpha_dummy_421, fv_syn_cid] using (nb090_compact_fv_empty_0340 A)

theorem nb090_wpp_notmem_1585 (h : Var) : (nb090_alpha_dummy_422 h) ∉ ((syn_cid)).fv := by
  simpa only [nb090_alpha_dummy_422, fv_syn_cid] using (nb090_compact_fv_empty_0341 h)

theorem nb090_wpp_notmem_1586 (A : Class) : (nb090_alpha_dummy_419 A) ∉ ((syn_cid)).fv :=
  by simpa only [nb090_alpha_dummy_419, fv_syn_cid] using (nb090_compact_fv_empty_0342 A)

theorem nb090_wpp_notmem_1587 (h : Var) : (nb090_alpha_dummy_420 h) ∉ ((syn_cid)).fv := by
  simpa only [nb090_alpha_dummy_420, fv_syn_cid] using (nb090_compact_fv_empty_0343 h)

theorem nb090_compact_envfresh_0196 (v : Var) (u : Var) (A : Class) (h : Var) :
    TEnvFresh
      [((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      ((syn_cid)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb090_alpha_dummy_421 A) (nb090_alpha_dummy_422 h)
      (nb090_wpp_notmem_1584 A) (nb090_wpp_notmem_1585 h)
      (TEnvFresh.consFresh (nb090_alpha_dummy_419 A) (nb090_alpha_dummy_420 h)
        (nb090_wpp_notmem_1586 A) (nb090_wpp_notmem_1587 h)
        (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0606 A)
          (nb090_wpp_notmem_0607 h)
          (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0608 A)
            (nb090_wpp_notmem_0609 v)
            (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0610 A)
              (nb090_wpp_notmem_0611 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A)
                (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0612 A)
                (nb090_wpp_notmem_0613 v u A h) (TEnvFresh.nil ((syn_cid)).fv)))))))

@[expose]
noncomputable def nb090_wpp_refl_0196 (v : Var) (u : Var) (A : Class) (h : Var) :
    TReflOn
      [((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      ((syn_cid)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0196 v u A h)


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
