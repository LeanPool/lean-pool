/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C077C001Block006

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C077C001Part020`. -/


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
noncomputable def nb077_split_alpha_0008 (x : Var) (F : Class) (I : Class) :
    TAlphaWff
      [((nb077_alpha_dummy_189 F I), (nb077_alpha_dummy_190 x)),
        ((nb077_alpha_dummy_187 F I), (nb077_alpha_dummy_188 x)),
        ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)),
        ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
        ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)),
        ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)),
        ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
        ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
        ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
      (Wff.imp (Wff.classMem (Class.cv (nb077_alpha_dummy_189 F I))
          (Class.cab (nb077_alpha_dummy_183 F I)
            (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_139 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb077_alpha_dummy_189 F I))
            (Class.cab (nb077_alpha_dummy_183 F I)
              (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_139 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb077_alpha_dummy_190 x))
          (Class.cab (nb077_alpha_dummy_185 x)
            (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_142 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_186 x))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb077_alpha_dummy_190 x))
            (Class.cab (nb077_alpha_dummy_185 x)
              (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_142 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_186 x))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb077_alpha_dummy_139 F I) ≠ (nb077_alpha_dummy_184 F I) from (by
                      unfold nb077_alpha_dummy_184;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb077_support_mem_0170 F I) 1))))
                  (show (nb077_alpha_dummy_142 x) ≠ (nb077_alpha_dummy_186 x) from (by
                      unfold nb077_alpha_dummy_186;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0172 x) 1))))
                  (TAlphaVar.there
                    (show (nb077_alpha_dummy_139 F I) ≠ (nb077_alpha_dummy_183 F I) from (by
                        unfold nb077_alpha_dummy_183;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0170 F I) 0))))
                    (show (nb077_alpha_dummy_142 x) ≠ (nb077_alpha_dummy_185 x) from (by
                        unfold nb077_alpha_dummy_185;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0172 x) 0)))) (TAlphaVar.there
                      (show (nb077_alpha_dummy_139 F I) ≠ (nb077_alpha_dummy_189 F I) from (by
                          unfold nb077_alpha_dummy_189;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0174 F I) 0))))
                      (show (nb077_alpha_dummy_142 x) ≠ (nb077_alpha_dummy_190 x) from (by
                          unfold nb077_alpha_dummy_190;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0175 x) 0))))
                      (TAlphaVar.there
                        (show (nb077_alpha_dummy_139 F I) ≠ (nb077_alpha_dummy_187 F I) from (by
                            unfold nb077_alpha_dummy_187;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0171 F I) 0))))
                        (show (nb077_alpha_dummy_142 x) ≠ (nb077_alpha_dummy_188 x) from (by
                            unfold nb077_alpha_dummy_188;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0173 x) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                                  (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I))
                                    (syn_c1c)))).fv ∪ ((syn_c1st)).fv) (by decide))
                          (freshVar_injective (((syn_cmpt x (syn_cvv)
                                  (syn_cplc (Class.cv x) (syn_c1c)))).fv ∪ ((syn_c1st)).fv)
                            (by decide)) (TAlphaVar.there (freshVar_injective
                              (((syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                                    (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I))
                                      (syn_c1c)))).fv ∪ ((syn_c1st)).fv) (by decide))
                            (freshVar_injective (((syn_cmpt x (syn_cvv)
                                    (syn_cplc (Class.cv x) (syn_c1c)))).fv ∪ ((syn_c1st)).fv)
                              (by decide)) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪
                      ((Class.cv (nb077_alpha_dummy_141 F I))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪
                      ((Class.cv (nb077_alpha_dummy_144 x))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb077_alpha_dummy_184 F I) ≠ (nb077_alpha_dummy_191 F I) from
                            (by
                              unfold nb077_alpha_dummy_191;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0176 F I) 0))))
                          (show (nb077_alpha_dummy_186 x) ≠ (nb077_alpha_dummy_193 x) from (by
                              unfold nb077_alpha_dummy_193;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0177 x) 0))))
                          (TAlphaVar.there (show
                              (nb077_alpha_dummy_184 F I) ≠ (nb077_alpha_dummy_192 F I) from (by
                                unfold nb077_alpha_dummy_192;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0176 F I) 1))))
                            (show (nb077_alpha_dummy_186 x) ≠ (nb077_alpha_dummy_194 x) from (by
                                unfold nb077_alpha_dummy_194;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0177 x) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb077_alpha_dummy_184 F I))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb077_alpha_dummy_186 x))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_191 F I) ≠ (nb077_alpha_dummy_198 F I) from
        (by
          unfold nb077_alpha_dummy_198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0180 F I) 1)))) (show (nb077_alpha_dummy_193 x) ≠
        (nb077_alpha_dummy_201 x) from (by
          unfold nb077_alpha_dummy_201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0181 x) 1)))) (TAlphaVar.there (show
        (nb077_alpha_dummy_191 F I) ≠ (nb077_alpha_dummy_197 F I) from (by
          unfold nb077_alpha_dummy_197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0180 F I)
                  0)))) (show (nb077_alpha_dummy_193 x) ≠ (nb077_alpha_dummy_200 x) from (by
          unfold nb077_alpha_dummy_200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0181 x) 0)))) (TAlphaVar.there (show
        (nb077_alpha_dummy_191 F I) ≠ (nb077_alpha_dummy_195 F I) from (by
          unfold nb077_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0178 F I)
                  0)))) (show (nb077_alpha_dummy_193 x) ≠ (nb077_alpha_dummy_196 x) from (by
          unfold nb077_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0179 x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_199 F I), (nb077_alpha_dummy_202 x)), ((nb077_alpha_dummy_198 F I),
        (nb077_alpha_dummy_201 x)), ((nb077_alpha_dummy_197 F I), (nb077_alpha_dummy_200 x)),
        ((nb077_alpha_dummy_195 F I), (nb077_alpha_dummy_196 x)), ((nb077_alpha_dummy_191 F I),
        (nb077_alpha_dummy_193 x)), ((nb077_alpha_dummy_192 F I), (nb077_alpha_dummy_194 x)),
        ((nb077_alpha_dummy_184 F I), (nb077_alpha_dummy_186 x)), ((nb077_alpha_dummy_183 F I),
        (nb077_alpha_dummy_185 x)), ((nb077_alpha_dummy_189 F I), (nb077_alpha_dummy_190 x)),
        ((nb077_alpha_dummy_187 F I), (nb077_alpha_dummy_188 x)), ((nb077_alpha_dummy_141 F I),
        (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
        ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I),
        (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I),
        (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_198 F I) ≠ (nb077_alpha_dummy_205 F I) from
        (by
          unfold
            nb077_alpha_dummy_205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0184
                    F I)
                  0)))) (show (nb077_alpha_dummy_201 x) ≠ (nb077_alpha_dummy_206 x) from (by
          unfold
            nb077_alpha_dummy_206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0185
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_198 F I) ≠
        (nb077_alpha_dummy_203 F I) from (by
          unfold
            nb077_alpha_dummy_203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0182
                    F I)
                  0)))) (show (nb077_alpha_dummy_201 x) ≠ (nb077_alpha_dummy_204 x) from (by
          unfold
            nb077_alpha_dummy_204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0183
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_191
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_199 F I) ≠ (nb077_alpha_dummy_205 F I) from
        (by
          unfold
            nb077_alpha_dummy_205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0188
                    F I)
                  0)))) (show (nb077_alpha_dummy_202 x) ≠ (nb077_alpha_dummy_206 x) from (by
          unfold
            nb077_alpha_dummy_206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0189
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_199 F I) ≠
        (nb077_alpha_dummy_203 F I) from (by
          unfold
            nb077_alpha_dummy_203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0186
                    F I)
                  0)))) (show (nb077_alpha_dummy_202 x) ≠ (nb077_alpha_dummy_204 x) from (by
          unfold
            nb077_alpha_dummy_204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0187
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_198 F I) ≠ (nb077_alpha_dummy_205 F I) from
        (by
          unfold
            nb077_alpha_dummy_205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0184
                    F I)
                  0)))) (show (nb077_alpha_dummy_201 x) ≠ (nb077_alpha_dummy_206 x) from (by
          unfold
            nb077_alpha_dummy_206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0185
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_198 F I) ≠
        (nb077_alpha_dummy_203 F I) from (by
          unfold
            nb077_alpha_dummy_203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0182
                    F I)
                  0)))) (show (nb077_alpha_dummy_201 x) ≠ (nb077_alpha_dummy_204 x) from (by
          unfold
            nb077_alpha_dummy_204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0183
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_191
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_199 F I) ≠ (nb077_alpha_dummy_205 F I) from
        (by
          unfold
            nb077_alpha_dummy_205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0188
                    F I)
                  0)))) (show (nb077_alpha_dummy_202 x) ≠ (nb077_alpha_dummy_206 x) from (by
          unfold
            nb077_alpha_dummy_206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0189
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_199 F I) ≠
        (nb077_alpha_dummy_203 F I) from (by
          unfold
            nb077_alpha_dummy_203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0186
                    F I)
                  0)))) (show (nb077_alpha_dummy_202 x) ≠ (nb077_alpha_dummy_204 x) from (by
          unfold
            nb077_alpha_dummy_204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0187
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_199 F I), (nb077_alpha_dummy_202 x)), ((nb077_alpha_dummy_198 F I),
        (nb077_alpha_dummy_201 x)), ((nb077_alpha_dummy_197 F I), (nb077_alpha_dummy_200 x)),
        ((nb077_alpha_dummy_195 F I), (nb077_alpha_dummy_196 x)), ((nb077_alpha_dummy_191 F I),
        (nb077_alpha_dummy_193 x)), ((nb077_alpha_dummy_192 F I), (nb077_alpha_dummy_194 x)),
        ((nb077_alpha_dummy_184 F I), (nb077_alpha_dummy_186 x)), ((nb077_alpha_dummy_183 F I),
        (nb077_alpha_dummy_185 x)), ((nb077_alpha_dummy_189 F I), (nb077_alpha_dummy_190 x)),
        ((nb077_alpha_dummy_187 F I), (nb077_alpha_dummy_188 x)), ((nb077_alpha_dummy_141 F I),
        (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
        ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I),
        (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I),
        (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_198
        F I) ≠ (nb077_alpha_dummy_209 F I) from (by
          unfold
            nb077_alpha_dummy_209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0192
                    F I)
                  0)))) (show (nb077_alpha_dummy_201 x) ≠ (nb077_alpha_dummy_210 x) from (by
          unfold
            nb077_alpha_dummy_210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0193
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_198 F I) ≠
        (nb077_alpha_dummy_207 F I) from (by
          unfold
            nb077_alpha_dummy_207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0190
                    F I)
                  0)))) (show (nb077_alpha_dummy_201 x) ≠ (nb077_alpha_dummy_208 x) from (by
          unfold
            nb077_alpha_dummy_208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0191
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_191
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_198 F I) ≠ (nb077_alpha_dummy_209 F I) from
        (by
          unfold
            nb077_alpha_dummy_209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0192
                    F I)
                  0)))) (show (nb077_alpha_dummy_201 x) ≠ (nb077_alpha_dummy_210 x) from (by
          unfold
            nb077_alpha_dummy_210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0193
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_198 F I) ≠
        (nb077_alpha_dummy_207 F I) from (by
          unfold
            nb077_alpha_dummy_207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0190
                    F I)
                  0)))) (show (nb077_alpha_dummy_201 x) ≠ (nb077_alpha_dummy_208 x) from (by
          unfold
            nb077_alpha_dummy_208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0191
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_191
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_199
        F I) ≠ (nb077_alpha_dummy_211 F I) from (by
          unfold
            nb077_alpha_dummy_211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0196
                    F I)
                  0)))) (show (nb077_alpha_dummy_202 x) ≠ (nb077_alpha_dummy_212 x) from (by
          unfold
            nb077_alpha_dummy_212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0197
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_199 F I) ≠
        (nb077_alpha_dummy_207 F I) from (by
          unfold
            nb077_alpha_dummy_207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0194
                    F I)
                  0)))) (show (nb077_alpha_dummy_202 x) ≠ (nb077_alpha_dummy_208 x) from (by
          unfold
            nb077_alpha_dummy_208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0195
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_199
        F I) ≠ (nb077_alpha_dummy_211 F I) from (by
          unfold
            nb077_alpha_dummy_211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0196
                    F I)
                  0)))) (show (nb077_alpha_dummy_202 x) ≠ (nb077_alpha_dummy_212 x) from (by
          unfold
            nb077_alpha_dummy_212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0197
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_199 F I) ≠
        (nb077_alpha_dummy_207 F I) from (by
          unfold
            nb077_alpha_dummy_207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0194
                    F I)
                  0)))) (show (nb077_alpha_dummy_202 x) ≠ (nb077_alpha_dummy_208 x) from (by
          unfold
            nb077_alpha_dummy_208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0195
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077_alpha_dummy_191 F I) ≠ (nb077_alpha_dummy_195 F I)
                                      from (by
                                        unfold nb077_alpha_dummy_195;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0178 F I) 0)))) (show
                                      (nb077_alpha_dummy_193 x) ≠ (nb077_alpha_dummy_196 x) from
                                      (by
                                        unfold nb077_alpha_dummy_196;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0179 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed [((nb077_alpha_dummy_195 F I),
                                      (nb077_alpha_dummy_196 x)), ((nb077_alpha_dummy_191 F I),
                                      (nb077_alpha_dummy_193 x)), ((nb077_alpha_dummy_192 F I),
                                      (nb077_alpha_dummy_194 x)), ((nb077_alpha_dummy_184 F I),
                                      (nb077_alpha_dummy_186 x)), ((nb077_alpha_dummy_183 F I),
                                      (nb077_alpha_dummy_185 x)), ((nb077_alpha_dummy_189 F I),
                                      (nb077_alpha_dummy_190 x)), ((nb077_alpha_dummy_187 F I),
                                      (nb077_alpha_dummy_188 x)), ((nb077_alpha_dummy_141 F I),
                                      (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I),
                                      (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I),
                                      (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I),
                                      (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I),
                                      (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I),
                                      (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I),
                                      (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I),
                                      (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I),
                                      (nb077_alpha_dummy_058 x F)),
                                    ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
                                    ((nb077_alpha_dummy_016 F I),
                                      (nb077_alpha_dummy_018 x F I)),
                                    ((nb077_alpha_dummy_015 F I),
                                      (nb077_alpha_dummy_017 x F I)),
                                    ((nb077_alpha_dummy_013 F I),
                                      (nb077_alpha_dummy_014 x F I)),
                                    ((nb077_alpha_dummy_011 F I),
                                      (nb077_alpha_dummy_012 x F I)),
                                    ((nb077_alpha_dummy_001 F I),
                                      (nb077_alpha_dummy_002 x F I)),
                                    ((nb077_alpha_dummy_004 F I),
                                      (nb077_alpha_dummy_006 x F I)),
                                    ((nb077_alpha_dummy_003 F I),
                                      (nb077_alpha_dummy_005 x F I))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb077_alpha_dummy_191 F I) ≠ (nb077_alpha_dummy_195 F I)
                                    from (by
                                      unfold nb077_alpha_dummy_195;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0178 F I)
                                              0)))) (show
                                    (nb077_alpha_dummy_193 x) ≠ (nb077_alpha_dummy_196 x) from
                                    (by
                                      unfold nb077_alpha_dummy_196;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0179 x)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077_alpha_dummy_191 F I) ≠ (nb077_alpha_dummy_195 F I)
                                      from (by
                                        unfold nb077_alpha_dummy_195;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0178 F I) 0)))) (show
                                      (nb077_alpha_dummy_193 x) ≠ (nb077_alpha_dummy_196 x) from
                                      (by
                                        unfold nb077_alpha_dummy_196;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0179 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed [((nb077_alpha_dummy_195 F I),
                                      (nb077_alpha_dummy_196 x)), ((nb077_alpha_dummy_191 F I),
                                      (nb077_alpha_dummy_193 x)), ((nb077_alpha_dummy_192 F I),
                                      (nb077_alpha_dummy_194 x)), ((nb077_alpha_dummy_184 F I),
                                      (nb077_alpha_dummy_186 x)), ((nb077_alpha_dummy_183 F I),
                                      (nb077_alpha_dummy_185 x)), ((nb077_alpha_dummy_189 F I),
                                      (nb077_alpha_dummy_190 x)), ((nb077_alpha_dummy_187 F I),
                                      (nb077_alpha_dummy_188 x)), ((nb077_alpha_dummy_141 F I),
                                      (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I),
                                      (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I),
                                      (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I),
                                      (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I),
                                      (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I),
                                      (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I),
                                      (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I),
                                      (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I),
                                      (nb077_alpha_dummy_058 x F)),
                                    ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
                                    ((nb077_alpha_dummy_016 F I),
                                      (nb077_alpha_dummy_018 x F I)),
                                    ((nb077_alpha_dummy_015 F I),
                                      (nb077_alpha_dummy_017 x F I)),
                                    ((nb077_alpha_dummy_013 F I),
                                      (nb077_alpha_dummy_014 x F I)),
                                    ((nb077_alpha_dummy_011 F I),
                                      (nb077_alpha_dummy_012 x F I)),
                                    ((nb077_alpha_dummy_001 F I),
                                      (nb077_alpha_dummy_002 x F I)),
                                    ((nb077_alpha_dummy_004 F I),
                                      (nb077_alpha_dummy_006 x F I)),
                                    ((nb077_alpha_dummy_003 F I),
                                      (nb077_alpha_dummy_005 x F I))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb077_alpha_dummy_139 F I) ≠ (nb077_alpha_dummy_184 F I) from (by
                        unfold nb077_alpha_dummy_184;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0170 F I) 1))))
                    (show (nb077_alpha_dummy_142 x) ≠ (nb077_alpha_dummy_186 x) from (by
                        unfold nb077_alpha_dummy_186;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0172 x) 1)))) (TAlphaVar.there
                      (show (nb077_alpha_dummy_139 F I) ≠ (nb077_alpha_dummy_183 F I) from (by
                          unfold nb077_alpha_dummy_183;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0170 F I) 0))))
                      (show (nb077_alpha_dummy_142 x) ≠ (nb077_alpha_dummy_185 x) from (by
                          unfold nb077_alpha_dummy_185;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0172 x) 0))))
                      (TAlphaVar.there
                        (show (nb077_alpha_dummy_139 F I) ≠ (nb077_alpha_dummy_189 F I) from (by
                            unfold nb077_alpha_dummy_189;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0174 F I) 0))))
                        (show (nb077_alpha_dummy_142 x) ≠ (nb077_alpha_dummy_190 x) from (by
                            unfold nb077_alpha_dummy_190;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0175 x) 0))))
                        (TAlphaVar.there
                          (show (nb077_alpha_dummy_139 F I) ≠ (nb077_alpha_dummy_187 F I) from
                            (by
                              unfold nb077_alpha_dummy_187;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0171 F I) 0))))
                          (show (nb077_alpha_dummy_142 x) ≠ (nb077_alpha_dummy_188 x) from (by
                              unfold nb077_alpha_dummy_188;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0173 x) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                                    (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I))
                                      (syn_c1c)))).fv ∪ ((syn_c1st)).fv) (by decide))
                            (freshVar_injective (((syn_cmpt x (syn_cvv)
                                    (syn_cplc (Class.cv x) (syn_c1c)))).fv ∪ ((syn_c1st)).fv)
                              (by decide)) (TAlphaVar.there (freshVar_injective
                                (((syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                                      (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I))
                                        (syn_c1c)))).fv ∪ ((syn_c1st)).fv) (by decide))
                              (freshVar_injective (((syn_cmpt x (syn_cvv)
                                      (syn_cplc (Class.cv x) (syn_c1c)))).fv ∪ ((syn_c1st)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪
                        ((Class.cv (nb077_alpha_dummy_141 F I))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪
                        ((Class.cv (nb077_alpha_dummy_144 x))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077_alpha_dummy_184 F I) ≠ (nb077_alpha_dummy_191 F I) from (by
                                unfold nb077_alpha_dummy_191;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0176 F I) 0))))
                            (show (nb077_alpha_dummy_186 x) ≠ (nb077_alpha_dummy_193 x) from (by
                                unfold nb077_alpha_dummy_193;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0177 x) 0))))
                            (TAlphaVar.there (show
                                (nb077_alpha_dummy_184 F I) ≠ (nb077_alpha_dummy_192 F I) from
                                (by
                                  unfold nb077_alpha_dummy_192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0176 F I)
                                          1))))
                              (show (nb077_alpha_dummy_186 x) ≠ (nb077_alpha_dummy_194 x) from
                                (by
                                  unfold nb077_alpha_dummy_194;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0177 x) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb077_alpha_dummy_184 F I))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb077_alpha_dummy_186 x))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_191 F I) ≠ (nb077_alpha_dummy_198 F I) from (by
          unfold nb077_alpha_dummy_198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0180 F I)
                  1)))) (show (nb077_alpha_dummy_193 x) ≠ (nb077_alpha_dummy_201 x) from (by
          unfold nb077_alpha_dummy_201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0181 x) 1)))) (TAlphaVar.there (show
        (nb077_alpha_dummy_191 F I) ≠ (nb077_alpha_dummy_197 F I) from (by
          unfold nb077_alpha_dummy_197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0180 F I)
                  0)))) (show (nb077_alpha_dummy_193 x) ≠ (nb077_alpha_dummy_200 x) from (by
          unfold nb077_alpha_dummy_200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0181 x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_191 F I) ≠
        (nb077_alpha_dummy_195 F I) from (by
          unfold nb077_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0178 F I)
                  0)))) (show (nb077_alpha_dummy_193 x) ≠ (nb077_alpha_dummy_196 x) from (by
          unfold nb077_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0179 x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_199 F I), (nb077_alpha_dummy_202 x)), ((nb077_alpha_dummy_198 F I),
        (nb077_alpha_dummy_201 x)), ((nb077_alpha_dummy_197 F I), (nb077_alpha_dummy_200 x)),
        ((nb077_alpha_dummy_195 F I), (nb077_alpha_dummy_196 x)), ((nb077_alpha_dummy_191 F I),
        (nb077_alpha_dummy_193 x)), ((nb077_alpha_dummy_192 F I), (nb077_alpha_dummy_194 x)),
        ((nb077_alpha_dummy_184 F I), (nb077_alpha_dummy_186 x)), ((nb077_alpha_dummy_183 F I),
        (nb077_alpha_dummy_185 x)), ((nb077_alpha_dummy_189 F I), (nb077_alpha_dummy_190 x)),
        ((nb077_alpha_dummy_187 F I), (nb077_alpha_dummy_188 x)), ((nb077_alpha_dummy_141 F I),
        (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
        ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I),
        (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I),
        (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_198 F I) ≠ (nb077_alpha_dummy_205 F I) from
        (by
          unfold
            nb077_alpha_dummy_205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0184
                    F I)
                  0)))) (show (nb077_alpha_dummy_201 x) ≠ (nb077_alpha_dummy_206 x) from (by
          unfold
            nb077_alpha_dummy_206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0185
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_198 F I) ≠
        (nb077_alpha_dummy_203 F I) from (by
          unfold
            nb077_alpha_dummy_203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0182
                    F I)
                  0)))) (show (nb077_alpha_dummy_201 x) ≠ (nb077_alpha_dummy_204 x) from (by
          unfold
            nb077_alpha_dummy_204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0183
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_191
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_199 F I) ≠ (nb077_alpha_dummy_205 F I) from
        (by
          unfold
            nb077_alpha_dummy_205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0188
                    F I)
                  0)))) (show (nb077_alpha_dummy_202 x) ≠ (nb077_alpha_dummy_206 x) from (by
          unfold
            nb077_alpha_dummy_206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0189
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_199 F I) ≠
        (nb077_alpha_dummy_203 F I) from (by
          unfold
            nb077_alpha_dummy_203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0186
                    F I)
                  0)))) (show (nb077_alpha_dummy_202 x) ≠ (nb077_alpha_dummy_204 x) from (by
          unfold
            nb077_alpha_dummy_204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0187
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_198 F I) ≠ (nb077_alpha_dummy_205 F I) from
        (by
          unfold
            nb077_alpha_dummy_205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0184
                    F I)
                  0)))) (show (nb077_alpha_dummy_201 x) ≠ (nb077_alpha_dummy_206 x) from (by
          unfold
            nb077_alpha_dummy_206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0185
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_198 F I) ≠
        (nb077_alpha_dummy_203 F I) from (by
          unfold
            nb077_alpha_dummy_203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0182
                    F I)
                  0)))) (show (nb077_alpha_dummy_201 x) ≠ (nb077_alpha_dummy_204 x) from (by
          unfold
            nb077_alpha_dummy_204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0183
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_191
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_199 F I) ≠ (nb077_alpha_dummy_205 F I) from
        (by
          unfold
            nb077_alpha_dummy_205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0188
                    F I)
                  0)))) (show (nb077_alpha_dummy_202 x) ≠ (nb077_alpha_dummy_206 x) from (by
          unfold
            nb077_alpha_dummy_206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0189
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_199 F I) ≠
        (nb077_alpha_dummy_203 F I) from (by
          unfold
            nb077_alpha_dummy_203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0186
                    F I)
                  0)))) (show (nb077_alpha_dummy_202 x) ≠ (nb077_alpha_dummy_204 x) from (by
          unfold
            nb077_alpha_dummy_204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0187
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_199 F I), (nb077_alpha_dummy_202 x)), ((nb077_alpha_dummy_198 F I),
        (nb077_alpha_dummy_201 x)), ((nb077_alpha_dummy_197 F I), (nb077_alpha_dummy_200 x)),
        ((nb077_alpha_dummy_195 F I), (nb077_alpha_dummy_196 x)), ((nb077_alpha_dummy_191 F I),
        (nb077_alpha_dummy_193 x)), ((nb077_alpha_dummy_192 F I), (nb077_alpha_dummy_194 x)),
        ((nb077_alpha_dummy_184 F I), (nb077_alpha_dummy_186 x)), ((nb077_alpha_dummy_183 F I),
        (nb077_alpha_dummy_185 x)), ((nb077_alpha_dummy_189 F I), (nb077_alpha_dummy_190 x)),
        ((nb077_alpha_dummy_187 F I), (nb077_alpha_dummy_188 x)), ((nb077_alpha_dummy_141 F I),
        (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
        ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I),
        (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I),
        (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_193
        x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_198
        F I) ≠ (nb077_alpha_dummy_209 F I) from (by
          unfold
            nb077_alpha_dummy_209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0192
                    F I)
                  0)))) (show (nb077_alpha_dummy_201 x) ≠ (nb077_alpha_dummy_210 x) from (by
          unfold
            nb077_alpha_dummy_210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0193
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_198 F I) ≠
        (nb077_alpha_dummy_207 F I) from (by
          unfold
            nb077_alpha_dummy_207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0190
                    F I)
                  0)))) (show (nb077_alpha_dummy_201 x) ≠ (nb077_alpha_dummy_208 x) from (by
          unfold
            nb077_alpha_dummy_208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0191
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_191
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_198 F I) ≠ (nb077_alpha_dummy_209 F I) from
        (by
          unfold
            nb077_alpha_dummy_209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0192
                    F I)
                  0)))) (show (nb077_alpha_dummy_201 x) ≠ (nb077_alpha_dummy_210 x) from (by
          unfold
            nb077_alpha_dummy_210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0193
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_198 F I) ≠
        (nb077_alpha_dummy_207 F I) from (by
          unfold
            nb077_alpha_dummy_207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0190
                    F I)
                  0)))) (show (nb077_alpha_dummy_201 x) ≠ (nb077_alpha_dummy_208 x) from (by
          unfold
            nb077_alpha_dummy_208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0191
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_191
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_199
        F I) ≠ (nb077_alpha_dummy_211 F I) from (by
          unfold
            nb077_alpha_dummy_211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0196
                    F I)
                  0)))) (show (nb077_alpha_dummy_202 x) ≠ (nb077_alpha_dummy_212 x) from (by
          unfold
            nb077_alpha_dummy_212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0197
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_199 F I) ≠
        (nb077_alpha_dummy_207 F I) from (by
          unfold
            nb077_alpha_dummy_207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0194
                    F I)
                  0)))) (show (nb077_alpha_dummy_202 x) ≠ (nb077_alpha_dummy_208 x) from (by
          unfold
            nb077_alpha_dummy_208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0195
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_199
        F I) ≠ (nb077_alpha_dummy_211 F I) from (by
          unfold
            nb077_alpha_dummy_211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0196
                    F I)
                  0)))) (show (nb077_alpha_dummy_202 x) ≠ (nb077_alpha_dummy_212 x) from (by
          unfold
            nb077_alpha_dummy_212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0197
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_199 F I) ≠
        (nb077_alpha_dummy_207 F I) from (by
          unfold
            nb077_alpha_dummy_207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0194
                    F I)
                  0)))) (show (nb077_alpha_dummy_202 x) ≠ (nb077_alpha_dummy_208 x) from (by
          unfold
            nb077_alpha_dummy_208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0195
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb077_alpha_dummy_191 F I) ≠
        (nb077_alpha_dummy_195 F I) from (by
                                          unfold nb077_alpha_dummy_195;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0178 F I) 0)))) (show
                                        (nb077_alpha_dummy_193 x) ≠ (nb077_alpha_dummy_196 x)
                                        from (by
                                          unfold nb077_alpha_dummy_196;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0179 x) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb077_alpha_dummy_195 F I), (nb077_alpha_dummy_196 x)),
                                      ((nb077_alpha_dummy_191 F I), (nb077_alpha_dummy_193 x)),
                                      ((nb077_alpha_dummy_192 F I), (nb077_alpha_dummy_194 x)),
                                      ((nb077_alpha_dummy_184 F I), (nb077_alpha_dummy_186 x)),
                                      ((nb077_alpha_dummy_183 F I), (nb077_alpha_dummy_185 x)),
                                      ((nb077_alpha_dummy_189 F I), (nb077_alpha_dummy_190 x)),
                                      ((nb077_alpha_dummy_187 F I), (nb077_alpha_dummy_188 x)),
                                      ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)),
                                      ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
                                      ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)),
                                      ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)),
                                      ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
                                      ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
                                      ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
                                      ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
                                      ((nb077_alpha_dummy_057 F I),
                                        (nb077_alpha_dummy_058 x F)),
                                      ((nb077_alpha_dummy_055 F I),
                                        (nb077_alpha_dummy_056 x F)),
                                      ((nb077_alpha_dummy_016 F I),
                                        (nb077_alpha_dummy_018 x F I)),
                                      ((nb077_alpha_dummy_015 F I),
                                        (nb077_alpha_dummy_017 x F I)),
                                      ((nb077_alpha_dummy_013 F I),
                                        (nb077_alpha_dummy_014 x F I)),
                                      ((nb077_alpha_dummy_011 F I),
                                        (nb077_alpha_dummy_012 x F I)),
                                      ((nb077_alpha_dummy_001 F I),
                                        (nb077_alpha_dummy_002 x F I)),
                                      ((nb077_alpha_dummy_004 F I),
                                        (nb077_alpha_dummy_006 x F I)),
                                      ((nb077_alpha_dummy_003 F I),
                                        (nb077_alpha_dummy_005 x F I))]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077_alpha_dummy_191 F I) ≠ (nb077_alpha_dummy_195 F I)
                                      from (by
                                        unfold nb077_alpha_dummy_195;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0178 F I) 0)))) (show
                                      (nb077_alpha_dummy_193 x) ≠ (nb077_alpha_dummy_196 x) from
                                      (by
                                        unfold nb077_alpha_dummy_196;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0179 x)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb077_alpha_dummy_191 F I) ≠
        (nb077_alpha_dummy_195 F I) from (by
                                          unfold nb077_alpha_dummy_195;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0178 F I) 0)))) (show
                                        (nb077_alpha_dummy_193 x) ≠ (nb077_alpha_dummy_196 x)
                                        from (by
                                          unfold nb077_alpha_dummy_196;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0179 x) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb077_alpha_dummy_195 F I), (nb077_alpha_dummy_196 x)),
                                      ((nb077_alpha_dummy_191 F I), (nb077_alpha_dummy_193 x)),
                                      ((nb077_alpha_dummy_192 F I), (nb077_alpha_dummy_194 x)),
                                      ((nb077_alpha_dummy_184 F I), (nb077_alpha_dummy_186 x)),
                                      ((nb077_alpha_dummy_183 F I), (nb077_alpha_dummy_185 x)),
                                      ((nb077_alpha_dummy_189 F I), (nb077_alpha_dummy_190 x)),
                                      ((nb077_alpha_dummy_187 F I), (nb077_alpha_dummy_188 x)),
                                      ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)),
                                      ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
                                      ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)),
                                      ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)),
                                      ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
                                      ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
                                      ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
                                      ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
                                      ((nb077_alpha_dummy_057 F I),
                                        (nb077_alpha_dummy_058 x F)),
                                      ((nb077_alpha_dummy_055 F I),
                                        (nb077_alpha_dummy_056 x F)),
                                      ((nb077_alpha_dummy_016 F I),
                                        (nb077_alpha_dummy_018 x F I)),
                                      ((nb077_alpha_dummy_015 F I),
                                        (nb077_alpha_dummy_017 x F I)),
                                      ((nb077_alpha_dummy_013 F I),
                                        (nb077_alpha_dummy_014 x F I)),
                                      ((nb077_alpha_dummy_011 F I),
                                        (nb077_alpha_dummy_012 x F I)),
                                      ((nb077_alpha_dummy_001 F I),
                                        (nb077_alpha_dummy_002 x F I)),
                                      ((nb077_alpha_dummy_004 F I),
                                        (nb077_alpha_dummy_006 x F I)),
                                      ((nb077_alpha_dummy_003 F I),
                                        (nb077_alpha_dummy_005 x F I))] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C077C001Part021`. -/


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
noncomputable def nb077_split_alpha_0009 (x : Var) (F : Class) (I : Class) :
    TAlphaWff
      [((nb077_alpha_dummy_217 F I), (nb077_alpha_dummy_218 x)),
        ((nb077_alpha_dummy_215 F I), (nb077_alpha_dummy_216 x)),
        ((nb077_alpha_dummy_184 F I), (nb077_alpha_dummy_186 x)),
        ((nb077_alpha_dummy_183 F I), (nb077_alpha_dummy_185 x)),
        ((nb077_alpha_dummy_213 F I), (nb077_alpha_dummy_214 x)),
        ((nb077_alpha_dummy_187 F I), (nb077_alpha_dummy_188 x)),
        ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)),
        ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
        ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)),
        ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)),
        ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
        ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
        ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
      (Wff.imp (Wff.classMem (Class.cv (nb077_alpha_dummy_217 F I))
          (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))) (Wff.neg
          (Wff.classMem (Class.cv (nb077_alpha_dummy_217 F I))
            (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I))))))
      (Wff.imp (Wff.classMem (Class.cv (nb077_alpha_dummy_218 x))
          (syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))) (Wff.neg
          (Wff.classMem (Class.cv (nb077_alpha_dummy_218 x))
            (syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb077_alpha_dummy_184 F I) ≠ (nb077_alpha_dummy_191 F I) from (by
                      unfold nb077_alpha_dummy_191;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb077_support_mem_0176 F I) 0))))
                  (show (nb077_alpha_dummy_186 x) ≠ (nb077_alpha_dummy_193 x) from (by
                      unfold nb077_alpha_dummy_193;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0177 x) 0))))
                  (TAlphaVar.there
                    (show (nb077_alpha_dummy_184 F I) ≠ (nb077_alpha_dummy_192 F I) from (by
                        unfold nb077_alpha_dummy_192;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0176 F I) 1))))
                    (show (nb077_alpha_dummy_186 x) ≠ (nb077_alpha_dummy_194 x) from (by
                        unfold nb077_alpha_dummy_194;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0177 x) 1)))) (TAlphaVar.there
                      (show (nb077_alpha_dummy_184 F I) ≠ (nb077_alpha_dummy_217 F I) from (by
                          unfold nb077_alpha_dummy_217;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0206 F I) 0))))
                      (show (nb077_alpha_dummy_186 x) ≠ (nb077_alpha_dummy_218 x) from (by
                          unfold nb077_alpha_dummy_218;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0207 x) 0))))
                      (TAlphaVar.there
                        (show (nb077_alpha_dummy_184 F I) ≠ (nb077_alpha_dummy_215 F I) from (by
                            unfold nb077_alpha_dummy_215;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0204 F I) 0))))
                        (show (nb077_alpha_dummy_186 x) ≠ (nb077_alpha_dummy_216 x) from (by
                            unfold nb077_alpha_dummy_216;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0205 x) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there
                  (freshVar_injective (((Class.cv (nb077_alpha_dummy_184 F I))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb077_alpha_dummy_186 x))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077_alpha_dummy_191 F I) ≠ (nb077_alpha_dummy_198 F I)
                                      from (by
                                        unfold nb077_alpha_dummy_198;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0180 F I) 1)))) (show
                                      (nb077_alpha_dummy_193 x) ≠ (nb077_alpha_dummy_201 x) from
                                      (by
                                        unfold nb077_alpha_dummy_201;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0181 x)
                                                1)))) (TAlphaVar.there (show
                                        (nb077_alpha_dummy_191 F I) ≠
        (nb077_alpha_dummy_197 F I) from (by
                                          unfold nb077_alpha_dummy_197;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0180 F I) 0)))) (show
                                        (nb077_alpha_dummy_193 x) ≠ (nb077_alpha_dummy_200 x)
                                        from (by
                                          unfold nb077_alpha_dummy_200;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0181 x) 0))))
                                      (TAlphaVar.there (show (nb077_alpha_dummy_191 F I) ≠
        (nb077_alpha_dummy_195 F I) from (by
          unfold nb077_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0178 F I) 0)))) (show (nb077_alpha_dummy_193 x) ≠
        (nb077_alpha_dummy_196 x) from (by
          unfold nb077_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0179 x) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb077_alpha_dummy_199 F I),
        (nb077_alpha_dummy_202 x)), ((nb077_alpha_dummy_198 F I), (nb077_alpha_dummy_201 x)),
                                        ((nb077_alpha_dummy_197 F I),
        (nb077_alpha_dummy_200 x)), ((nb077_alpha_dummy_195 F I), (nb077_alpha_dummy_196 x)),
                                        ((nb077_alpha_dummy_191 F I),
        (nb077_alpha_dummy_193 x)), ((nb077_alpha_dummy_192 F I), (nb077_alpha_dummy_194 x)),
                                        ((nb077_alpha_dummy_217 F I),
        (nb077_alpha_dummy_218 x)), ((nb077_alpha_dummy_215 F I), (nb077_alpha_dummy_216 x)),
                                        ((nb077_alpha_dummy_184 F I),
        (nb077_alpha_dummy_186 x)), ((nb077_alpha_dummy_183 F I), (nb077_alpha_dummy_185 x)),
                                        ((nb077_alpha_dummy_213 F I),
        (nb077_alpha_dummy_214 x)), ((nb077_alpha_dummy_187 F I), (nb077_alpha_dummy_188 x)),
                                        ((nb077_alpha_dummy_141 F I),
        (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
                                        ((nb077_alpha_dummy_139 F I),
        (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)),
                                        ((nb077_alpha_dummy_061 F I),
        (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
                                        ((nb077_alpha_dummy_059 F I),
        (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
                                        ((nb077_alpha_dummy_057 F I),
        (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I),
        (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I),
        (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I),
        (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I),
        (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I),
        (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I),
        (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I),
        (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I),
        (nb077_alpha_dummy_005 x F I))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_198 F I) ≠ (nb077_alpha_dummy_205 F I) from (by
          unfold
            nb077_alpha_dummy_205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0184
                    F I)
                  0)))) (show (nb077_alpha_dummy_201 x) ≠ (nb077_alpha_dummy_206 x) from (by
          unfold
            nb077_alpha_dummy_206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0185
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_198 F I) ≠
        (nb077_alpha_dummy_203 F I) from (by
          unfold
            nb077_alpha_dummy_203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0182
                    F I)
                  0)))) (show (nb077_alpha_dummy_201 x) ≠ (nb077_alpha_dummy_204 x) from (by
          unfold
            nb077_alpha_dummy_204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0183
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_191
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_199 F I) ≠
        (nb077_alpha_dummy_205 F I) from (by
          unfold
            nb077_alpha_dummy_205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0188
                    F I)
                  0)))) (show (nb077_alpha_dummy_202 x) ≠ (nb077_alpha_dummy_206 x) from (by
          unfold
            nb077_alpha_dummy_206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0189
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_199 F I) ≠
        (nb077_alpha_dummy_203 F I) from (by
          unfold
            nb077_alpha_dummy_203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0186
                    F I)
                  0)))) (show (nb077_alpha_dummy_202 x) ≠ (nb077_alpha_dummy_204 x) from (by
          unfold
            nb077_alpha_dummy_204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0187
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_198 F I) ≠ (nb077_alpha_dummy_205 F I) from
        (by
          unfold
            nb077_alpha_dummy_205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0184
                    F I)
                  0)))) (show (nb077_alpha_dummy_201 x) ≠ (nb077_alpha_dummy_206 x) from (by
          unfold
            nb077_alpha_dummy_206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0185
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_198 F I) ≠
        (nb077_alpha_dummy_203 F I) from (by
          unfold
            nb077_alpha_dummy_203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0182
                    F I)
                  0)))) (show (nb077_alpha_dummy_201 x) ≠ (nb077_alpha_dummy_204 x) from (by
          unfold
            nb077_alpha_dummy_204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0183
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_191
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_199 F I) ≠
        (nb077_alpha_dummy_205 F I) from (by
          unfold
            nb077_alpha_dummy_205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0188
                    F I)
                  0)))) (show (nb077_alpha_dummy_202 x) ≠ (nb077_alpha_dummy_206 x) from (by
          unfold
            nb077_alpha_dummy_206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0189
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_199 F I) ≠
        (nb077_alpha_dummy_203 F I) from (by
          unfold
            nb077_alpha_dummy_203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0186
                    F I)
                  0)))) (show (nb077_alpha_dummy_202 x) ≠ (nb077_alpha_dummy_204 x) from (by
          unfold
            nb077_alpha_dummy_204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0187
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb077_alpha_dummy_199 F I),
        (nb077_alpha_dummy_202 x)), ((nb077_alpha_dummy_198 F I), (nb077_alpha_dummy_201 x)),
        ((nb077_alpha_dummy_197 F I), (nb077_alpha_dummy_200 x)), ((nb077_alpha_dummy_195 F I),
        (nb077_alpha_dummy_196 x)), ((nb077_alpha_dummy_191 F I), (nb077_alpha_dummy_193 x)),
        ((nb077_alpha_dummy_192 F I), (nb077_alpha_dummy_194 x)), ((nb077_alpha_dummy_217 F I),
        (nb077_alpha_dummy_218 x)), ((nb077_alpha_dummy_215 F I), (nb077_alpha_dummy_216 x)),
        ((nb077_alpha_dummy_184 F I), (nb077_alpha_dummy_186 x)), ((nb077_alpha_dummy_183 F I),
        (nb077_alpha_dummy_185 x)), ((nb077_alpha_dummy_213 F I), (nb077_alpha_dummy_214 x)),
        ((nb077_alpha_dummy_187 F I), (nb077_alpha_dummy_188 x)), ((nb077_alpha_dummy_141 F I),
        (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
        ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I),
        (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I),
        (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
                                        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_198 F I) ≠ (nb077_alpha_dummy_209 F I) from (by
          unfold
            nb077_alpha_dummy_209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0192
                    F I)
                  0)))) (show (nb077_alpha_dummy_201 x) ≠ (nb077_alpha_dummy_210 x) from (by
          unfold
            nb077_alpha_dummy_210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0193
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_198 F I) ≠
        (nb077_alpha_dummy_207 F I) from (by
          unfold
            nb077_alpha_dummy_207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0190
                    F I)
                  0)))) (show (nb077_alpha_dummy_201 x) ≠ (nb077_alpha_dummy_208 x) from (by
          unfold
            nb077_alpha_dummy_208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0191
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_191
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_198 F I) ≠
        (nb077_alpha_dummy_209 F I) from (by
          unfold
            nb077_alpha_dummy_209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0192
                    F I)
                  0)))) (show (nb077_alpha_dummy_201 x) ≠ (nb077_alpha_dummy_210 x) from (by
          unfold
            nb077_alpha_dummy_210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0193
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_198 F I) ≠
        (nb077_alpha_dummy_207 F I) from (by
          unfold
            nb077_alpha_dummy_207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0190
                    F I)
                  0)))) (show (nb077_alpha_dummy_201 x) ≠ (nb077_alpha_dummy_208 x) from (by
          unfold
            nb077_alpha_dummy_208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0191
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_191
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_199 F I) ≠ (nb077_alpha_dummy_211 F I) from (by
          unfold
            nb077_alpha_dummy_211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0196
                    F I)
                  0)))) (show (nb077_alpha_dummy_202 x) ≠ (nb077_alpha_dummy_212 x) from (by
          unfold
            nb077_alpha_dummy_212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0197
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_199 F I) ≠
        (nb077_alpha_dummy_207 F I) from (by
          unfold
            nb077_alpha_dummy_207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0194
                    F I)
                  0)))) (show (nb077_alpha_dummy_202 x) ≠ (nb077_alpha_dummy_208 x) from (by
          unfold
            nb077_alpha_dummy_208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0195
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_199 F I) ≠ (nb077_alpha_dummy_211 F I) from (by
          unfold
            nb077_alpha_dummy_211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0196
                    F I)
                  0)))) (show (nb077_alpha_dummy_202 x) ≠ (nb077_alpha_dummy_212 x) from (by
          unfold
            nb077_alpha_dummy_212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0197
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_199 F I) ≠
        (nb077_alpha_dummy_207 F I) from (by
          unfold
            nb077_alpha_dummy_207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0194
                    F I)
                  0)))) (show (nb077_alpha_dummy_202 x) ≠ (nb077_alpha_dummy_208 x) from (by
          unfold
            nb077_alpha_dummy_208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0195
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077_alpha_dummy_191 F I) ≠ (nb077_alpha_dummy_195 F I) from (by
                                unfold nb077_alpha_dummy_195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0178 F I) 0))))
                            (show (nb077_alpha_dummy_193 x) ≠ (nb077_alpha_dummy_196 x) from (by
                                unfold nb077_alpha_dummy_196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0179 x) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb077_alpha_dummy_195 F I), (nb077_alpha_dummy_196 x)),
                            ((nb077_alpha_dummy_191 F I), (nb077_alpha_dummy_193 x)),
                            ((nb077_alpha_dummy_192 F I), (nb077_alpha_dummy_194 x)),
                            ((nb077_alpha_dummy_217 F I), (nb077_alpha_dummy_218 x)),
                            ((nb077_alpha_dummy_215 F I), (nb077_alpha_dummy_216 x)),
                            ((nb077_alpha_dummy_184 F I), (nb077_alpha_dummy_186 x)),
                            ((nb077_alpha_dummy_183 F I), (nb077_alpha_dummy_185 x)),
                            ((nb077_alpha_dummy_213 F I), (nb077_alpha_dummy_214 x)),
                            ((nb077_alpha_dummy_187 F I), (nb077_alpha_dummy_188 x)),
                            ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)),
                            ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
                            ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)),
                            ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)),
                            ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
                            ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
                            ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
                            ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
                            ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
                            ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
                            ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
                            ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
                            ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
                            ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
                            ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
                            ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
                            ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb077_alpha_dummy_191 F I) ≠ (nb077_alpha_dummy_195 F I) from
                            (by
                              unfold nb077_alpha_dummy_195;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0178 F I) 0))))
                          (show (nb077_alpha_dummy_193 x) ≠ (nb077_alpha_dummy_196 x) from (by
                              unfold nb077_alpha_dummy_196;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0179 x) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077_alpha_dummy_191 F I) ≠ (nb077_alpha_dummy_195 F I) from (by
                                unfold nb077_alpha_dummy_195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0178 F I) 0))))
                            (show (nb077_alpha_dummy_193 x) ≠ (nb077_alpha_dummy_196 x) from (by
                                unfold nb077_alpha_dummy_196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0179 x) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb077_alpha_dummy_195 F I), (nb077_alpha_dummy_196 x)),
                            ((nb077_alpha_dummy_191 F I), (nb077_alpha_dummy_193 x)),
                            ((nb077_alpha_dummy_192 F I), (nb077_alpha_dummy_194 x)),
                            ((nb077_alpha_dummy_217 F I), (nb077_alpha_dummy_218 x)),
                            ((nb077_alpha_dummy_215 F I), (nb077_alpha_dummy_216 x)),
                            ((nb077_alpha_dummy_184 F I), (nb077_alpha_dummy_186 x)),
                            ((nb077_alpha_dummy_183 F I), (nb077_alpha_dummy_185 x)),
                            ((nb077_alpha_dummy_213 F I), (nb077_alpha_dummy_214 x)),
                            ((nb077_alpha_dummy_187 F I), (nb077_alpha_dummy_188 x)),
                            ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)),
                            ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
                            ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)),
                            ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)),
                            ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
                            ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
                            ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
                            ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
                            ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
                            ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
                            ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
                            ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
                            ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
                            ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
                            ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
                            ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
                            ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb077_alpha_dummy_184 F I) ≠ (nb077_alpha_dummy_191 F I) from (by
                        unfold nb077_alpha_dummy_191;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0176 F I) 0))))
                    (show (nb077_alpha_dummy_186 x) ≠ (nb077_alpha_dummy_193 x) from (by
                        unfold nb077_alpha_dummy_193;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0177 x) 0)))) (TAlphaVar.there
                      (show (nb077_alpha_dummy_184 F I) ≠ (nb077_alpha_dummy_192 F I) from (by
                          unfold nb077_alpha_dummy_192;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0176 F I) 1))))
                      (show (nb077_alpha_dummy_186 x) ≠ (nb077_alpha_dummy_194 x) from (by
                          unfold nb077_alpha_dummy_194;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0177 x) 1))))
                      (TAlphaVar.there
                        (show (nb077_alpha_dummy_184 F I) ≠ (nb077_alpha_dummy_217 F I) from (by
                            unfold nb077_alpha_dummy_217;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0206 F I) 0))))
                        (show (nb077_alpha_dummy_186 x) ≠ (nb077_alpha_dummy_218 x) from (by
                            unfold nb077_alpha_dummy_218;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0207 x) 0))))
                        (TAlphaVar.there
                          (show (nb077_alpha_dummy_184 F I) ≠ (nb077_alpha_dummy_215 F I) from
                            (by
                              unfold nb077_alpha_dummy_215;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0204 F I) 0))))
                          (show (nb077_alpha_dummy_186 x) ≠ (nb077_alpha_dummy_216 x) from (by
                              unfold nb077_alpha_dummy_216;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0205 x) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb077_alpha_dummy_184 F I))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb077_alpha_dummy_186 x))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb077_alpha_dummy_191 F I) ≠
        (nb077_alpha_dummy_198 F I) from (by
                                          unfold nb077_alpha_dummy_198;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0180 F I) 1)))) (show
                                        (nb077_alpha_dummy_193 x) ≠ (nb077_alpha_dummy_201 x)
                                        from (by
                                          unfold nb077_alpha_dummy_201;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0181 x) 1))))
                                      (TAlphaVar.there (show (nb077_alpha_dummy_191 F I) ≠
        (nb077_alpha_dummy_197 F I) from (by
          unfold nb077_alpha_dummy_197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0180 F I) 0)))) (show (nb077_alpha_dummy_193 x) ≠
        (nb077_alpha_dummy_200 x) from (by
          unfold nb077_alpha_dummy_200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0181 x) 0)))) (TAlphaVar.there (show
        (nb077_alpha_dummy_191 F I) ≠ (nb077_alpha_dummy_195 F I) from (by
          unfold nb077_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0178 F I) 0)))) (show (nb077_alpha_dummy_193 x) ≠
        (nb077_alpha_dummy_196 x) from (by
          unfold nb077_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0179 x) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb077_alpha_dummy_199 F I),
        (nb077_alpha_dummy_202 x)), ((nb077_alpha_dummy_198 F I), (nb077_alpha_dummy_201 x)),
        ((nb077_alpha_dummy_197 F I), (nb077_alpha_dummy_200 x)), ((nb077_alpha_dummy_195 F I),
        (nb077_alpha_dummy_196 x)), ((nb077_alpha_dummy_191 F I), (nb077_alpha_dummy_193 x)),
        ((nb077_alpha_dummy_192 F I), (nb077_alpha_dummy_194 x)), ((nb077_alpha_dummy_217 F I),
        (nb077_alpha_dummy_218 x)), ((nb077_alpha_dummy_215 F I), (nb077_alpha_dummy_216 x)),
        ((nb077_alpha_dummy_184 F I), (nb077_alpha_dummy_186 x)), ((nb077_alpha_dummy_183 F I),
        (nb077_alpha_dummy_185 x)), ((nb077_alpha_dummy_213 F I), (nb077_alpha_dummy_214 x)),
        ((nb077_alpha_dummy_187 F I), (nb077_alpha_dummy_188 x)), ((nb077_alpha_dummy_141 F I),
        (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
        ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I),
        (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I),
        (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
                                        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_198 F
        I) ≠ (nb077_alpha_dummy_205 F I) from (by
          unfold
            nb077_alpha_dummy_205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0184
                    F I)
                  0)))) (show (nb077_alpha_dummy_201 x) ≠ (nb077_alpha_dummy_206 x) from (by
          unfold
            nb077_alpha_dummy_206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0185
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_198 F I) ≠
        (nb077_alpha_dummy_203 F I) from (by
          unfold
            nb077_alpha_dummy_203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0182
                    F I)
                  0)))) (show (nb077_alpha_dummy_201 x) ≠ (nb077_alpha_dummy_204 x) from (by
          unfold
            nb077_alpha_dummy_204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0183
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_191
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_199 F I) ≠ (nb077_alpha_dummy_205 F I) from
        (by
          unfold
            nb077_alpha_dummy_205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0188
                    F I)
                  0)))) (show (nb077_alpha_dummy_202 x) ≠ (nb077_alpha_dummy_206 x) from (by
          unfold
            nb077_alpha_dummy_206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0189
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_199 F I) ≠
        (nb077_alpha_dummy_203 F I) from (by
          unfold
            nb077_alpha_dummy_203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0186
                    F I)
                  0)))) (show (nb077_alpha_dummy_202 x) ≠ (nb077_alpha_dummy_204 x) from (by
          unfold
            nb077_alpha_dummy_204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0187
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_198 F I) ≠ (nb077_alpha_dummy_205 F I) from
        (by
          unfold
            nb077_alpha_dummy_205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0184
                    F I)
                  0)))) (show (nb077_alpha_dummy_201 x) ≠ (nb077_alpha_dummy_206 x) from (by
          unfold
            nb077_alpha_dummy_206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0185
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_198 F I) ≠
        (nb077_alpha_dummy_203 F I) from (by
          unfold
            nb077_alpha_dummy_203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0182
                    F I)
                  0)))) (show (nb077_alpha_dummy_201 x) ≠ (nb077_alpha_dummy_204 x) from (by
          unfold
            nb077_alpha_dummy_204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0183
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_191
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_199 F I) ≠ (nb077_alpha_dummy_205 F I) from
        (by
          unfold
            nb077_alpha_dummy_205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0188
                    F I)
                  0)))) (show (nb077_alpha_dummy_202 x) ≠ (nb077_alpha_dummy_206 x) from (by
          unfold
            nb077_alpha_dummy_206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0189
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_199 F I) ≠
        (nb077_alpha_dummy_203 F I) from (by
          unfold
            nb077_alpha_dummy_203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0186
                    F I)
                  0)))) (show (nb077_alpha_dummy_202 x) ≠ (nb077_alpha_dummy_204 x) from (by
          unfold
            nb077_alpha_dummy_204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0187
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_199 F I), (nb077_alpha_dummy_202 x)), ((nb077_alpha_dummy_198 F I),
        (nb077_alpha_dummy_201 x)), ((nb077_alpha_dummy_197 F I), (nb077_alpha_dummy_200 x)),
        ((nb077_alpha_dummy_195 F I), (nb077_alpha_dummy_196 x)), ((nb077_alpha_dummy_191 F I),
        (nb077_alpha_dummy_193 x)), ((nb077_alpha_dummy_192 F I), (nb077_alpha_dummy_194 x)),
        ((nb077_alpha_dummy_217 F I), (nb077_alpha_dummy_218 x)), ((nb077_alpha_dummy_215 F I),
        (nb077_alpha_dummy_216 x)), ((nb077_alpha_dummy_184 F I), (nb077_alpha_dummy_186 x)),
        ((nb077_alpha_dummy_183 F I), (nb077_alpha_dummy_185 x)), ((nb077_alpha_dummy_213 F I),
        (nb077_alpha_dummy_214 x)), ((nb077_alpha_dummy_187 F I), (nb077_alpha_dummy_188 x)),
        ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I),
        (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)),
        ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I),
        (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
        ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I),
        (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_198 F
        I) ≠ (nb077_alpha_dummy_209 F I) from (by
          unfold
            nb077_alpha_dummy_209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0192
                    F I)
                  0)))) (show (nb077_alpha_dummy_201 x) ≠ (nb077_alpha_dummy_210 x) from (by
          unfold
            nb077_alpha_dummy_210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0193
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_198 F I) ≠
        (nb077_alpha_dummy_207 F I) from (by
          unfold
            nb077_alpha_dummy_207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0190
                    F I)
                  0)))) (show (nb077_alpha_dummy_201 x) ≠ (nb077_alpha_dummy_208 x) from (by
          unfold
            nb077_alpha_dummy_208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0191
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_191
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_198 F I) ≠ (nb077_alpha_dummy_209 F I) from
        (by
          unfold
            nb077_alpha_dummy_209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0192
                    F I)
                  0)))) (show (nb077_alpha_dummy_201 x) ≠ (nb077_alpha_dummy_210 x) from (by
          unfold
            nb077_alpha_dummy_210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0193
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_198 F I) ≠
        (nb077_alpha_dummy_207 F I) from (by
          unfold
            nb077_alpha_dummy_207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0190
                    F I)
                  0)))) (show (nb077_alpha_dummy_201 x) ≠ (nb077_alpha_dummy_208 x) from (by
          unfold
            nb077_alpha_dummy_208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0191
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_191
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_199 F
        I) ≠ (nb077_alpha_dummy_211 F I) from (by
          unfold
            nb077_alpha_dummy_211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0196
                    F I)
                  0)))) (show (nb077_alpha_dummy_202 x) ≠ (nb077_alpha_dummy_212 x) from (by
          unfold
            nb077_alpha_dummy_212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0197
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_199 F I) ≠
        (nb077_alpha_dummy_207 F I) from (by
          unfold
            nb077_alpha_dummy_207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0194
                    F I)
                  0)))) (show (nb077_alpha_dummy_202 x) ≠ (nb077_alpha_dummy_208 x) from (by
          unfold
            nb077_alpha_dummy_208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0195
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_199 F
        I) ≠ (nb077_alpha_dummy_211 F I) from (by
          unfold
            nb077_alpha_dummy_211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0196
                    F I)
                  0)))) (show (nb077_alpha_dummy_202 x) ≠ (nb077_alpha_dummy_212 x) from (by
          unfold
            nb077_alpha_dummy_212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0197
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_199 F I) ≠
        (nb077_alpha_dummy_207 F I) from (by
          unfold
            nb077_alpha_dummy_207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0194
                    F I)
                  0)))) (show (nb077_alpha_dummy_202 x) ≠ (nb077_alpha_dummy_208 x) from (by
          unfold
            nb077_alpha_dummy_208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0195
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb077_alpha_dummy_191 F I) ≠ (nb077_alpha_dummy_195 F I) from
                                (by
                                  unfold nb077_alpha_dummy_195;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0178 F I)
                                          0))))
                              (show (nb077_alpha_dummy_193 x) ≠ (nb077_alpha_dummy_196 x) from
                                (by
                                  unfold nb077_alpha_dummy_196;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0179 x) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb077_alpha_dummy_195 F I), (nb077_alpha_dummy_196 x)),
                              ((nb077_alpha_dummy_191 F I), (nb077_alpha_dummy_193 x)),
                              ((nb077_alpha_dummy_192 F I), (nb077_alpha_dummy_194 x)),
                              ((nb077_alpha_dummy_217 F I), (nb077_alpha_dummy_218 x)),
                              ((nb077_alpha_dummy_215 F I), (nb077_alpha_dummy_216 x)),
                              ((nb077_alpha_dummy_184 F I), (nb077_alpha_dummy_186 x)),
                              ((nb077_alpha_dummy_183 F I), (nb077_alpha_dummy_185 x)),
                              ((nb077_alpha_dummy_213 F I), (nb077_alpha_dummy_214 x)),
                              ((nb077_alpha_dummy_187 F I), (nb077_alpha_dummy_188 x)),
                              ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)),
                              ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
                              ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)),
                              ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)),
                              ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
                              ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
                              ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
                              ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
                              ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
                              ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
                              ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
                              ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
                              ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
                              ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
                              ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
                              ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
                              ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077_alpha_dummy_191 F I) ≠ (nb077_alpha_dummy_195 F I) from (by
                                unfold nb077_alpha_dummy_195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0178 F I) 0))))
                            (show (nb077_alpha_dummy_193 x) ≠ (nb077_alpha_dummy_196 x) from (by
                                unfold nb077_alpha_dummy_196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0179 x) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb077_alpha_dummy_191 F I) ≠ (nb077_alpha_dummy_195 F I) from
                                (by
                                  unfold nb077_alpha_dummy_195;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0178 F I)
                                          0))))
                              (show (nb077_alpha_dummy_193 x) ≠ (nb077_alpha_dummy_196 x) from
                                (by
                                  unfold nb077_alpha_dummy_196;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0179 x) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb077_alpha_dummy_195 F I), (nb077_alpha_dummy_196 x)),
                              ((nb077_alpha_dummy_191 F I), (nb077_alpha_dummy_193 x)),
                              ((nb077_alpha_dummy_192 F I), (nb077_alpha_dummy_194 x)),
                              ((nb077_alpha_dummy_217 F I), (nb077_alpha_dummy_218 x)),
                              ((nb077_alpha_dummy_215 F I), (nb077_alpha_dummy_216 x)),
                              ((nb077_alpha_dummy_184 F I), (nb077_alpha_dummy_186 x)),
                              ((nb077_alpha_dummy_183 F I), (nb077_alpha_dummy_185 x)),
                              ((nb077_alpha_dummy_213 F I), (nb077_alpha_dummy_214 x)),
                              ((nb077_alpha_dummy_187 F I), (nb077_alpha_dummy_188 x)),
                              ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)),
                              ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
                              ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)),
                              ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)),
                              ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
                              ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
                              ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
                              ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
                              ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
                              ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
                              ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
                              ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
                              ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
                              ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
                              ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
                              ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
                              ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

theorem nb077_wpp_notmem_0556 (F : Class) (I : Class) :
    (nb077_alpha_dummy_141 F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_141, fv_syn_c1st] using (nb077_compact_fv_empty_0160 F I)

theorem nb077_wpp_notmem_0557 (x : Var) : (nb077_alpha_dummy_144 x) ∉ ((syn_c1st)).fv :=
  by simpa only [nb077_alpha_dummy_144, fv_syn_c1st] using (nb077_compact_fv_empty_0161 x)

theorem nb077_wpp_notmem_0558 (F : Class) (I : Class) :
    (nb077_alpha_dummy_140 F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_140, fv_syn_c1st] using (nb077_compact_fv_empty_0128 F I)

theorem nb077_wpp_notmem_0559 (x : Var) : (nb077_alpha_dummy_143 x) ∉ ((syn_c1st)).fv :=
  by simpa only [nb077_alpha_dummy_143, fv_syn_c1st] using (nb077_compact_fv_empty_0129 x)

theorem nb077_wpp_notmem_0560 (F : Class) (I : Class) :
    (nb077_alpha_dummy_139 F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_139, fv_syn_c1st] using (nb077_compact_fv_empty_0130 F I)

theorem nb077_wpp_notmem_0561 (x : Var) : (nb077_alpha_dummy_142 x) ∉ ((syn_c1st)).fv :=
  by simpa only [nb077_alpha_dummy_142, fv_syn_c1st] using (nb077_compact_fv_empty_0131 x)

theorem nb077_wpp_notmem_0562 (F : Class) (I : Class) :
    (nb077_alpha_dummy_145 F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_145, fv_syn_c1st] using (nb077_compact_fv_empty_0132 F I)

theorem nb077_wpp_notmem_0563 (x : Var) : (nb077_alpha_dummy_146 x) ∉ ((syn_c1st)).fv :=
  by simpa only [nb077_alpha_dummy_146, fv_syn_c1st] using (nb077_compact_fv_empty_0133 x)

theorem nb077_wpp_notmem_0564 (F : Class) (I : Class) :
    (nb077_alpha_dummy_061 F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_061, fv_syn_c1st] using (nb077_compact_fv_empty_0100 F I)

theorem nb077_wpp_notmem_0565 (x : Var) : (nb077_alpha_dummy_064 x) ∉ ((syn_c1st)).fv :=
  by simpa only [nb077_alpha_dummy_064, fv_syn_c1st] using (nb077_compact_fv_empty_0101 x)

theorem nb077_wpp_notmem_0566 (F : Class) (I : Class) :
    (nb077_alpha_dummy_060 F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_060, fv_syn_c1st] using (nb077_compact_fv_empty_0064 F I)

theorem nb077_wpp_notmem_0567 (x : Var) : (nb077_alpha_dummy_063 x) ∉ ((syn_c1st)).fv :=
  by simpa only [nb077_alpha_dummy_063, fv_syn_c1st] using (nb077_compact_fv_empty_0065 x)

theorem nb077_wpp_notmem_0568 (F : Class) (I : Class) :
    (nb077_alpha_dummy_059 F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_059, fv_syn_c1st] using (nb077_compact_fv_empty_0066 F I)

theorem nb077_wpp_notmem_0569 (x : Var) : (nb077_alpha_dummy_062 x) ∉ ((syn_c1st)).fv :=
  by simpa only [nb077_alpha_dummy_062, fv_syn_c1st] using (nb077_compact_fv_empty_0067 x)

theorem nb077_wpp_notmem_0570 (F : Class) (I : Class) :
    (nb077_alpha_dummy_065 F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_065, fv_syn_c1st] using (nb077_compact_fv_empty_0068 F I)

theorem nb077_wpp_notmem_0571 (x : Var) : (nb077_alpha_dummy_066 x) ∉ ((syn_c1st)).fv :=
  by simpa only [nb077_alpha_dummy_066, fv_syn_c1st] using (nb077_compact_fv_empty_0069 x)

theorem nb077_wpp_notmem_0572 (F : Class) (I : Class) :
    (nb077_alpha_dummy_057 F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_057, fv_syn_c1st] using (nb077_compact_fv_empty_0070 F I)

theorem nb077_wpp_notmem_0573 (x : Var) (F : Class) :
    (nb077_alpha_dummy_058 x F) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_058, fv_syn_c1st] using (nb077_compact_fv_empty_0071 x F)

theorem nb077_wpp_notmem_0574 (F : Class) (I : Class) :
    (nb077_alpha_dummy_055 F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_055, fv_syn_c1st] using (nb077_compact_fv_empty_0072 F I)

theorem nb077_wpp_notmem_0575 (x : Var) (F : Class) :
    (nb077_alpha_dummy_056 x F) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_056, fv_syn_c1st] using (nb077_compact_fv_empty_0073 x F)

theorem nb077_wpp_notmem_0576 (F : Class) (I : Class) :
    (nb077_alpha_dummy_016 F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_016, fv_syn_c1st] using (nb077_compact_fv_empty_0030 F I)

theorem nb077_wpp_notmem_0577 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_018 x F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_018, fv_syn_c1st] using
    (nb077_compact_fv_empty_0031 x F I)

theorem nb077_wpp_notmem_0578 (F : Class) (I : Class) :
    (nb077_alpha_dummy_015 F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_015, fv_syn_c1st] using (nb077_compact_fv_empty_0032 F I)

theorem nb077_wpp_notmem_0579 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_017 x F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_017, fv_syn_c1st] using
    (nb077_compact_fv_empty_0033 x F I)

theorem nb077_wpp_notmem_0580 (F : Class) (I : Class) :
    (nb077_alpha_dummy_013 F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_013, fv_syn_c1st] using (nb077_compact_fv_empty_0034 F I)

theorem nb077_wpp_notmem_0581 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_014 x F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_014, fv_syn_c1st] using
    (nb077_compact_fv_empty_0035 x F I)

theorem nb077_wpp_notmem_0582 (F : Class) (I : Class) :
    (nb077_alpha_dummy_011 F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_011, fv_syn_c1st] using (nb077_compact_fv_empty_0036 F I)

theorem nb077_wpp_notmem_0583 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_012 x F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_012, fv_syn_c1st] using
    (nb077_compact_fv_empty_0037 x F I)

theorem nb077_wpp_notmem_0584 (F : Class) (I : Class) :
    (nb077_alpha_dummy_001 F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_001, fv_syn_c1st] using (nb077_compact_fv_empty_0004 F I)

theorem nb077_wpp_notmem_0585 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_002 x F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_002, fv_syn_c1st] using
    (nb077_compact_fv_empty_0005 x F I)

theorem nb077_wpp_notmem_0586 (F : Class) (I : Class) :
    (nb077_alpha_dummy_004 F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_004, fv_syn_c1st] using (nb077_compact_fv_empty_0006 F I)

theorem nb077_wpp_notmem_0587 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_006 x F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_006, fv_syn_c1st] using
    (nb077_compact_fv_empty_0007 x F I)

theorem nb077_wpp_notmem_0588 (F : Class) (I : Class) :
    (nb077_alpha_dummy_003 F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_003, fv_syn_c1st] using (nb077_compact_fv_empty_0008 F I)

theorem nb077_wpp_notmem_0589 (x : Var) (F : Class) (I : Class) :
    (nb077_alpha_dummy_005 x F I) ∉ ((syn_c1st)).fv := by
  simpa only [nb077_alpha_dummy_005, fv_syn_c1st] using
    (nb077_compact_fv_empty_0009 x F I)

theorem nb077_compact_envfresh_0037 (x : Var) (F : Class) (I : Class) :
    TEnvFresh
      [((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)),
        ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
        ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)),
        ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)),
        ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
        ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
        ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
      ((syn_c1st)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb077_alpha_dummy_141 F I) (nb077_alpha_dummy_144 x)
      (nb077_wpp_notmem_0556 F I) (nb077_wpp_notmem_0557 x)
      (TEnvFresh.consFresh (nb077_alpha_dummy_140 F I) (nb077_alpha_dummy_143 x)
        (nb077_wpp_notmem_0558 F I) (nb077_wpp_notmem_0559 x)
        (TEnvFresh.consFresh (nb077_alpha_dummy_139 F I) (nb077_alpha_dummy_142 x)
          (nb077_wpp_notmem_0560 F I) (nb077_wpp_notmem_0561 x)
          (TEnvFresh.consFresh (nb077_alpha_dummy_145 F I) (nb077_alpha_dummy_146 x)
            (nb077_wpp_notmem_0562 F I) (nb077_wpp_notmem_0563 x)
            (TEnvFresh.consFresh (nb077_alpha_dummy_061 F I) (nb077_alpha_dummy_064 x)
              (nb077_wpp_notmem_0564 F I) (nb077_wpp_notmem_0565 x)
              (TEnvFresh.consFresh (nb077_alpha_dummy_060 F I) (nb077_alpha_dummy_063 x)
                (nb077_wpp_notmem_0566 F I) (nb077_wpp_notmem_0567 x)
                (TEnvFresh.consFresh (nb077_alpha_dummy_059 F I) (nb077_alpha_dummy_062 x)
                  (nb077_wpp_notmem_0568 F I) (nb077_wpp_notmem_0569 x)
                  (TEnvFresh.consFresh (nb077_alpha_dummy_065 F I)
                    (nb077_alpha_dummy_066 x) (nb077_wpp_notmem_0570 F I)
                    (nb077_wpp_notmem_0571 x) (TEnvFresh.consFresh (nb077_alpha_dummy_057 F I)
                      (nb077_alpha_dummy_058 x F) (nb077_wpp_notmem_0572 F I)
                      (nb077_wpp_notmem_0573 x F)
                      (TEnvFresh.consFresh (nb077_alpha_dummy_055 F I)
                        (nb077_alpha_dummy_056 x F) (nb077_wpp_notmem_0574 F I)
                        (nb077_wpp_notmem_0575 x F)
                        (TEnvFresh.consFresh (nb077_alpha_dummy_016 F I)
                          (nb077_alpha_dummy_018 x F I) (nb077_wpp_notmem_0576 F I)
                          (nb077_wpp_notmem_0577 x F I)
                          (TEnvFresh.consFresh (nb077_alpha_dummy_015 F I)
                            (nb077_alpha_dummy_017 x F I) (nb077_wpp_notmem_0578 F I)
                            (nb077_wpp_notmem_0579 x F I)
                            (TEnvFresh.consFresh (nb077_alpha_dummy_013 F I)
                              (nb077_alpha_dummy_014 x F I) (nb077_wpp_notmem_0580 F I)
                              (nb077_wpp_notmem_0581 x F I)
                              (TEnvFresh.consFresh (nb077_alpha_dummy_011 F I)
                                (nb077_alpha_dummy_012 x F I) (nb077_wpp_notmem_0582 F I)
                                (nb077_wpp_notmem_0583 x F I)
                                (TEnvFresh.consFresh (nb077_alpha_dummy_001 F I)
                                  (nb077_alpha_dummy_002 x F I) (nb077_wpp_notmem_0584 F I)
                                  (nb077_wpp_notmem_0585 x F I)
                                  (TEnvFresh.consFresh (nb077_alpha_dummy_004 F I)
                                    (nb077_alpha_dummy_006 x F I) (nb077_wpp_notmem_0586 F I)
                                    (nb077_wpp_notmem_0587 x F I)
                                    (TEnvFresh.consFresh (nb077_alpha_dummy_003 F I)
                                      (nb077_alpha_dummy_005 x F I) (nb077_wpp_notmem_0588 F I)
                                      (nb077_wpp_notmem_0589 x F I)
                                      (TEnvFresh.nil ((syn_c1st)).fv))))))))))))))))))

@[expose]
noncomputable def nb077_wpp_refl_0037 (x : Var) (F : Class) (I : Class) :
    TReflOn
      [((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)),
        ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
        ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)),
        ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)),
        ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
        ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
        ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
      ((syn_c1st)).fv :=
  TEnvFresh.reflOn (nb077_compact_envfresh_0037 x F I)


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
