/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C095M3Part015

/-! NF weak partition development: NAR4H5C095M3Part016. -/


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
noncomputable def nb095_split_alpha_0020 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_201 D R S_cls E), (nb095_alpha_dummy_202 f)),
        ((nb095_alpha_dummy_170 D R S_cls E), (nb095_alpha_dummy_172 f)),
        ((nb095_alpha_dummy_169 D R S_cls E), (nb095_alpha_dummy_171 f)),
        ((nb095_alpha_dummy_199 D R S_cls E), (nb095_alpha_dummy_200 f)),
        ((nb095_alpha_dummy_173 D R S_cls E), (nb095_alpha_dummy_174 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb095_alpha_dummy_201 D R S_cls E))
            (syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E)))))
          (Wff.classMem (Class.cv (nb095_alpha_dummy_201 D R S_cls E))
            (syn_ccompl (syn_csn (syn_c0c))))))
      (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb095_alpha_dummy_202 f))
            (syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_172 f)))))
          (Wff.classMem (Class.cv (nb095_alpha_dummy_202 f))
            (syn_ccompl (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_170 D R S_cls E) ≠
                                (nb095_alpha_dummy_177 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_177;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0178 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_172 f) ≠ (nb095_alpha_dummy_179 f) from (by
                                unfold nb095_alpha_dummy_179;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0179 f) 0))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_170 D R S_cls E) ≠
                                  (nb095_alpha_dummy_178 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_178;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0178 D R S_cls E) 1))))
                              (show (nb095_alpha_dummy_172 f) ≠ (nb095_alpha_dummy_180 f) from
                                (by
                                  unfold nb095_alpha_dummy_180;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0179 f) 1))))
                              (TAlphaVar.there (show (nb095_alpha_dummy_170 D R S_cls E) ≠
                                    (nb095_alpha_dummy_203 D R S_cls E) from (by
                                    unfold nb095_alpha_dummy_203;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0208 D R S_cls E) 0)))) (show
                                  (nb095_alpha_dummy_172 f) ≠ (nb095_alpha_dummy_204 f) from (by
                                    unfold nb095_alpha_dummy_204;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0209 f)
                                            0)))) (TAlphaVar.there (show
                                    (nb095_alpha_dummy_170 D R S_cls E) ≠
                                      (nb095_alpha_dummy_201 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_201;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0206 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_172 f) ≠ (nb095_alpha_dummy_202 f) from
                                    (by
                                      unfold nb095_alpha_dummy_202;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0207 f)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_170 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_172 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_177 D R S_cls E) ≠ (nb095_alpha_dummy_184 D R S_cls E) from (by
          unfold nb095_alpha_dummy_184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0182 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_179 f) ≠ (nb095_alpha_dummy_187 f) from (by
          unfold nb095_alpha_dummy_187;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0183 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_177 D R S_cls E) ≠ (nb095_alpha_dummy_183 D R S_cls E) from (by
          unfold nb095_alpha_dummy_183;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0182 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_179 f) ≠ (nb095_alpha_dummy_186 f) from (by
          unfold nb095_alpha_dummy_186;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0183 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_177 D R S_cls E) ≠
        (nb095_alpha_dummy_181 D R S_cls E) from (by
          unfold nb095_alpha_dummy_181;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0180 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_179 f) ≠ (nb095_alpha_dummy_182 f) from (by
          unfold nb095_alpha_dummy_182;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0181 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_185 D R S_cls E), (nb095_alpha_dummy_188 f)),
        ((nb095_alpha_dummy_184 D R S_cls E), (nb095_alpha_dummy_187 f)),
        ((nb095_alpha_dummy_183 D R S_cls E), (nb095_alpha_dummy_186 f)),
        ((nb095_alpha_dummy_181 D R S_cls E), (nb095_alpha_dummy_182 f)),
        ((nb095_alpha_dummy_177 D R S_cls E), (nb095_alpha_dummy_179 f)),
        ((nb095_alpha_dummy_178 D R S_cls E), (nb095_alpha_dummy_180 f)),
        ((nb095_alpha_dummy_203 D R S_cls E), (nb095_alpha_dummy_204 f)),
        ((nb095_alpha_dummy_201 D R S_cls E), (nb095_alpha_dummy_202 f)),
        ((nb095_alpha_dummy_170 D R S_cls E), (nb095_alpha_dummy_172 f)),
        ((nb095_alpha_dummy_169 D R S_cls E), (nb095_alpha_dummy_171 f)),
        ((nb095_alpha_dummy_199 D R S_cls E), (nb095_alpha_dummy_200 f)),
        ((nb095_alpha_dummy_173 D R S_cls E), (nb095_alpha_dummy_174 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_184
        D R S_cls E) ≠ (nb095_alpha_dummy_191 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0186
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_192 f) from (by
          unfold
            nb095_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0187
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠
        (nb095_alpha_dummy_189 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0184
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_190 f) from (by
          unfold
            nb095_alpha_dummy_190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0185
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_177
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_185 D R S_cls E) ≠ (nb095_alpha_dummy_191
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0190
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_192 f) from (by
          unfold
            nb095_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0191
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_185 D R S_cls E) ≠
        (nb095_alpha_dummy_189 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0188
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_190 f) from (by
          unfold
            nb095_alpha_dummy_190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0189
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠ (nb095_alpha_dummy_191
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0186
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_192 f) from (by
          unfold
            nb095_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0187
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠
        (nb095_alpha_dummy_189 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0184
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_190 f) from (by
          unfold
            nb095_alpha_dummy_190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0185
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_177
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_185 D R S_cls E) ≠ (nb095_alpha_dummy_191
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0190
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_192 f) from (by
          unfold
            nb095_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0191
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_185 D R S_cls E) ≠
        (nb095_alpha_dummy_189 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0188
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_190 f) from (by
          unfold
            nb095_alpha_dummy_190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0189
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_185 D R S_cls E), (nb095_alpha_dummy_188 f)),
        ((nb095_alpha_dummy_184 D R S_cls E), (nb095_alpha_dummy_187 f)),
        ((nb095_alpha_dummy_183 D R S_cls E), (nb095_alpha_dummy_186 f)),
        ((nb095_alpha_dummy_181 D R S_cls E), (nb095_alpha_dummy_182 f)),
        ((nb095_alpha_dummy_177 D R S_cls E), (nb095_alpha_dummy_179 f)),
        ((nb095_alpha_dummy_178 D R S_cls E), (nb095_alpha_dummy_180 f)),
        ((nb095_alpha_dummy_203 D R S_cls E), (nb095_alpha_dummy_204 f)),
        ((nb095_alpha_dummy_201 D R S_cls E), (nb095_alpha_dummy_202 f)),
        ((nb095_alpha_dummy_170 D R S_cls E), (nb095_alpha_dummy_172 f)),
        ((nb095_alpha_dummy_169 D R S_cls E), (nb095_alpha_dummy_171 f)),
        ((nb095_alpha_dummy_199 D R S_cls E), (nb095_alpha_dummy_200 f)),
        ((nb095_alpha_dummy_173 D R S_cls E), (nb095_alpha_dummy_174 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_177 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_177 D R
        S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠ (nb095_alpha_dummy_195
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0194
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_196 f) from (by
          unfold
            nb095_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0195
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠
        (nb095_alpha_dummy_193 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0192
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_194 f) from (by
          unfold
            nb095_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0193
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_177
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠ (nb095_alpha_dummy_195
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0194
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_196 f) from (by
          unfold
            nb095_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0195
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠
        (nb095_alpha_dummy_193 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0192
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_194 f) from (by
          unfold
            nb095_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0193
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_177
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_185
        D R S_cls E) ≠ (nb095_alpha_dummy_197 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0198
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_198 f) from (by
          unfold
            nb095_alpha_dummy_198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0199
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_185 D R S_cls E) ≠
        (nb095_alpha_dummy_193 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0196
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_194 f) from (by
          unfold
            nb095_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0197
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_185
        D R S_cls E) ≠ (nb095_alpha_dummy_197 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0198
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_198 f) from (by
          unfold
            nb095_alpha_dummy_198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0199
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_185 D R S_cls E) ≠
        (nb095_alpha_dummy_193 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0196
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_194 f) from (by
          unfold
            nb095_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0197
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_177 D R S_cls E) ≠
        (nb095_alpha_dummy_181 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_181;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0180 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_179 f) ≠
        (nb095_alpha_dummy_182 f) from (by
                                          unfold nb095_alpha_dummy_182;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0181 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_181 D R S_cls E),
                                        (nb095_alpha_dummy_182 f)),
                                      ((nb095_alpha_dummy_177 D R S_cls E),
                                        (nb095_alpha_dummy_179 f)),
                                      ((nb095_alpha_dummy_178 D R S_cls E),
                                        (nb095_alpha_dummy_180 f)),
                                      ((nb095_alpha_dummy_203 D R S_cls E),
                                        (nb095_alpha_dummy_204 f)),
                                      ((nb095_alpha_dummy_201 D R S_cls E),
                                        (nb095_alpha_dummy_202 f)),
                                      ((nb095_alpha_dummy_170 D R S_cls E),
                                        (nb095_alpha_dummy_172 f)),
                                      ((nb095_alpha_dummy_169 D R S_cls E),
                                        (nb095_alpha_dummy_171 f)),
                                      ((nb095_alpha_dummy_199 D R S_cls E),
                                        (nb095_alpha_dummy_200 f)),
                                      ((nb095_alpha_dummy_173 D R S_cls E),
                                        (nb095_alpha_dummy_174 f)),
                                      ((nb095_alpha_dummy_013 D R S_cls E),
                                        (nb095_alpha_dummy_016 f)),
                                      ((nb095_alpha_dummy_012 D R S_cls E),
                                        (nb095_alpha_dummy_015 f)),
                                      ((nb095_alpha_dummy_011 D R S_cls E),
                                        (nb095_alpha_dummy_014 f)),
                                      ((nb095_alpha_dummy_017 D R S_cls E),
                                        (nb095_alpha_dummy_018 f)),
                                      ((nb095_alpha_dummy_001 D R S_cls E), u),
                                      ((nb095_alpha_dummy_002 D R S_cls E), x),
                                      ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_177 D R S_cls E) ≠
                                        (nb095_alpha_dummy_181 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_181;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0180 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_179 f) ≠ (nb095_alpha_dummy_182 f) from
                                      (by
                                        unfold nb095_alpha_dummy_182;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0181 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_177 D R S_cls E) ≠
        (nb095_alpha_dummy_181 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_181;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0180 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_179 f) ≠
        (nb095_alpha_dummy_182 f) from (by
                                          unfold nb095_alpha_dummy_182;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0181 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_181 D R S_cls E),
                                        (nb095_alpha_dummy_182 f)),
                                      ((nb095_alpha_dummy_177 D R S_cls E),
                                        (nb095_alpha_dummy_179 f)),
                                      ((nb095_alpha_dummy_178 D R S_cls E),
                                        (nb095_alpha_dummy_180 f)),
                                      ((nb095_alpha_dummy_203 D R S_cls E),
                                        (nb095_alpha_dummy_204 f)),
                                      ((nb095_alpha_dummy_201 D R S_cls E),
                                        (nb095_alpha_dummy_202 f)),
                                      ((nb095_alpha_dummy_170 D R S_cls E),
                                        (nb095_alpha_dummy_172 f)),
                                      ((nb095_alpha_dummy_169 D R S_cls E),
                                        (nb095_alpha_dummy_171 f)),
                                      ((nb095_alpha_dummy_199 D R S_cls E),
                                        (nb095_alpha_dummy_200 f)),
                                      ((nb095_alpha_dummy_173 D R S_cls E),
                                        (nb095_alpha_dummy_174 f)),
                                      ((nb095_alpha_dummy_013 D R S_cls E),
                                        (nb095_alpha_dummy_016 f)),
                                      ((nb095_alpha_dummy_012 D R S_cls E),
                                        (nb095_alpha_dummy_015 f)),
                                      ((nb095_alpha_dummy_011 D R S_cls E),
                                        (nb095_alpha_dummy_014 f)),
                                      ((nb095_alpha_dummy_017 D R S_cls E),
                                        (nb095_alpha_dummy_018 f)),
                                      ((nb095_alpha_dummy_001 D R S_cls E), u),
                                      ((nb095_alpha_dummy_002 D R S_cls E), x),
                                      ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_170 D R S_cls E) ≠
                                (nb095_alpha_dummy_177 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_177;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0178 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_172 f) ≠ (nb095_alpha_dummy_179 f) from (by
                                unfold nb095_alpha_dummy_179;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0179 f) 0))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_170 D R S_cls E) ≠
                                  (nb095_alpha_dummy_178 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_178;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0178 D R S_cls E) 1))))
                              (show (nb095_alpha_dummy_172 f) ≠ (nb095_alpha_dummy_180 f) from
                                (by
                                  unfold nb095_alpha_dummy_180;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0179 f) 1))))
                              (TAlphaVar.there (show (nb095_alpha_dummy_170 D R S_cls E) ≠
                                    (nb095_alpha_dummy_203 D R S_cls E) from (by
                                    unfold nb095_alpha_dummy_203;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0208 D R S_cls E) 0)))) (show
                                  (nb095_alpha_dummy_172 f) ≠ (nb095_alpha_dummy_204 f) from (by
                                    unfold nb095_alpha_dummy_204;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0209 f)
                                            0)))) (TAlphaVar.there (show
                                    (nb095_alpha_dummy_170 D R S_cls E) ≠
                                      (nb095_alpha_dummy_201 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_201;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0206 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_172 f) ≠ (nb095_alpha_dummy_202 f) from
                                    (by
                                      unfold nb095_alpha_dummy_202;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0207 f)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_170 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_172 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_177 D R S_cls E) ≠ (nb095_alpha_dummy_184 D R S_cls E) from (by
          unfold nb095_alpha_dummy_184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0182 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_179 f) ≠ (nb095_alpha_dummy_187 f) from (by
          unfold nb095_alpha_dummy_187;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0183 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_177 D R S_cls E) ≠ (nb095_alpha_dummy_183 D R S_cls E) from (by
          unfold nb095_alpha_dummy_183;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0182 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_179 f) ≠ (nb095_alpha_dummy_186 f) from (by
          unfold nb095_alpha_dummy_186;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0183 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_177 D R S_cls E) ≠
        (nb095_alpha_dummy_181 D R S_cls E) from (by
          unfold nb095_alpha_dummy_181;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0180 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_179 f) ≠ (nb095_alpha_dummy_182 f) from (by
          unfold nb095_alpha_dummy_182;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0181 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_185 D R S_cls E), (nb095_alpha_dummy_188 f)),
        ((nb095_alpha_dummy_184 D R S_cls E), (nb095_alpha_dummy_187 f)),
        ((nb095_alpha_dummy_183 D R S_cls E), (nb095_alpha_dummy_186 f)),
        ((nb095_alpha_dummy_181 D R S_cls E), (nb095_alpha_dummy_182 f)),
        ((nb095_alpha_dummy_177 D R S_cls E), (nb095_alpha_dummy_179 f)),
        ((nb095_alpha_dummy_178 D R S_cls E), (nb095_alpha_dummy_180 f)),
        ((nb095_alpha_dummy_203 D R S_cls E), (nb095_alpha_dummy_204 f)),
        ((nb095_alpha_dummy_201 D R S_cls E), (nb095_alpha_dummy_202 f)),
        ((nb095_alpha_dummy_170 D R S_cls E), (nb095_alpha_dummy_172 f)),
        ((nb095_alpha_dummy_169 D R S_cls E), (nb095_alpha_dummy_171 f)),
        ((nb095_alpha_dummy_199 D R S_cls E), (nb095_alpha_dummy_200 f)),
        ((nb095_alpha_dummy_173 D R S_cls E), (nb095_alpha_dummy_174 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_184
        D R S_cls E) ≠ (nb095_alpha_dummy_191 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0186
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_192 f) from (by
          unfold
            nb095_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0187
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠
        (nb095_alpha_dummy_189 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0184
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_190 f) from (by
          unfold
            nb095_alpha_dummy_190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0185
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_177
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_185 D R S_cls E) ≠ (nb095_alpha_dummy_191
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0190
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_192 f) from (by
          unfold
            nb095_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0191
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_185 D R S_cls E) ≠
        (nb095_alpha_dummy_189 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0188
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_190 f) from (by
          unfold
            nb095_alpha_dummy_190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0189
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠ (nb095_alpha_dummy_191
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0186
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_192 f) from (by
          unfold
            nb095_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0187
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠
        (nb095_alpha_dummy_189 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0184
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_190 f) from (by
          unfold
            nb095_alpha_dummy_190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0185
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_177
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_185 D R S_cls E) ≠ (nb095_alpha_dummy_191
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0190
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_192 f) from (by
          unfold
            nb095_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0191
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_185 D R S_cls E) ≠
        (nb095_alpha_dummy_189 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0188
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_190 f) from (by
          unfold
            nb095_alpha_dummy_190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0189
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_185 D R S_cls E), (nb095_alpha_dummy_188 f)),
        ((nb095_alpha_dummy_184 D R S_cls E), (nb095_alpha_dummy_187 f)),
        ((nb095_alpha_dummy_183 D R S_cls E), (nb095_alpha_dummy_186 f)),
        ((nb095_alpha_dummy_181 D R S_cls E), (nb095_alpha_dummy_182 f)),
        ((nb095_alpha_dummy_177 D R S_cls E), (nb095_alpha_dummy_179 f)),
        ((nb095_alpha_dummy_178 D R S_cls E), (nb095_alpha_dummy_180 f)),
        ((nb095_alpha_dummy_203 D R S_cls E), (nb095_alpha_dummy_204 f)),
        ((nb095_alpha_dummy_201 D R S_cls E), (nb095_alpha_dummy_202 f)),
        ((nb095_alpha_dummy_170 D R S_cls E), (nb095_alpha_dummy_172 f)),
        ((nb095_alpha_dummy_169 D R S_cls E), (nb095_alpha_dummy_171 f)),
        ((nb095_alpha_dummy_199 D R S_cls E), (nb095_alpha_dummy_200 f)),
        ((nb095_alpha_dummy_173 D R S_cls E), (nb095_alpha_dummy_174 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_177 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_177 D R
        S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠ (nb095_alpha_dummy_195
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0194
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_196 f) from (by
          unfold
            nb095_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0195
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠
        (nb095_alpha_dummy_193 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0192
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_194 f) from (by
          unfold
            nb095_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0193
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_177
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠ (nb095_alpha_dummy_195
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0194
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_196 f) from (by
          unfold
            nb095_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0195
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠
        (nb095_alpha_dummy_193 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0192
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_194 f) from (by
          unfold
            nb095_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0193
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_177
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_185
        D R S_cls E) ≠ (nb095_alpha_dummy_197 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0198
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_198 f) from (by
          unfold
            nb095_alpha_dummy_198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0199
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_185 D R S_cls E) ≠
        (nb095_alpha_dummy_193 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0196
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_194 f) from (by
          unfold
            nb095_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0197
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_185
        D R S_cls E) ≠ (nb095_alpha_dummy_197 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0198
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_198 f) from (by
          unfold
            nb095_alpha_dummy_198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0199
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_185 D R S_cls E) ≠
        (nb095_alpha_dummy_193 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0196
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_194 f) from (by
          unfold
            nb095_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0197
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_177 D R S_cls E) ≠
        (nb095_alpha_dummy_181 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_181;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0180 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_179 f) ≠
        (nb095_alpha_dummy_182 f) from (by
                                          unfold nb095_alpha_dummy_182;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0181 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_181 D R S_cls E),
                                        (nb095_alpha_dummy_182 f)),
                                      ((nb095_alpha_dummy_177 D R S_cls E),
                                        (nb095_alpha_dummy_179 f)),
                                      ((nb095_alpha_dummy_178 D R S_cls E),
                                        (nb095_alpha_dummy_180 f)),
                                      ((nb095_alpha_dummy_203 D R S_cls E),
                                        (nb095_alpha_dummy_204 f)),
                                      ((nb095_alpha_dummy_201 D R S_cls E),
                                        (nb095_alpha_dummy_202 f)),
                                      ((nb095_alpha_dummy_170 D R S_cls E),
                                        (nb095_alpha_dummy_172 f)),
                                      ((nb095_alpha_dummy_169 D R S_cls E),
                                        (nb095_alpha_dummy_171 f)),
                                      ((nb095_alpha_dummy_199 D R S_cls E),
                                        (nb095_alpha_dummy_200 f)),
                                      ((nb095_alpha_dummy_173 D R S_cls E),
                                        (nb095_alpha_dummy_174 f)),
                                      ((nb095_alpha_dummy_013 D R S_cls E),
                                        (nb095_alpha_dummy_016 f)),
                                      ((nb095_alpha_dummy_012 D R S_cls E),
                                        (nb095_alpha_dummy_015 f)),
                                      ((nb095_alpha_dummy_011 D R S_cls E),
                                        (nb095_alpha_dummy_014 f)),
                                      ((nb095_alpha_dummy_017 D R S_cls E),
                                        (nb095_alpha_dummy_018 f)),
                                      ((nb095_alpha_dummy_001 D R S_cls E), u),
                                      ((nb095_alpha_dummy_002 D R S_cls E), x),
                                      ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_177 D R S_cls E) ≠
                                        (nb095_alpha_dummy_181 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_181;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0180 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_179 f) ≠ (nb095_alpha_dummy_182 f) from
                                      (by
                                        unfold nb095_alpha_dummy_182;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0181 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_177 D R S_cls E) ≠
        (nb095_alpha_dummy_181 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_181;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0180 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_179 f) ≠
        (nb095_alpha_dummy_182 f) from (by
                                          unfold nb095_alpha_dummy_182;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0181 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_181 D R S_cls E),
                                        (nb095_alpha_dummy_182 f)),
                                      ((nb095_alpha_dummy_177 D R S_cls E),
                                        (nb095_alpha_dummy_179 f)),
                                      ((nb095_alpha_dummy_178 D R S_cls E),
                                        (nb095_alpha_dummy_180 f)),
                                      ((nb095_alpha_dummy_203 D R S_cls E),
                                        (nb095_alpha_dummy_204 f)),
                                      ((nb095_alpha_dummy_201 D R S_cls E),
                                        (nb095_alpha_dummy_202 f)),
                                      ((nb095_alpha_dummy_170 D R S_cls E),
                                        (nb095_alpha_dummy_172 f)),
                                      ((nb095_alpha_dummy_169 D R S_cls E),
                                        (nb095_alpha_dummy_171 f)),
                                      ((nb095_alpha_dummy_199 D R S_cls E),
                                        (nb095_alpha_dummy_200 f)),
                                      ((nb095_alpha_dummy_173 D R S_cls E),
                                        (nb095_alpha_dummy_174 f)),
                                      ((nb095_alpha_dummy_013 D R S_cls E),
                                        (nb095_alpha_dummy_016 f)),
                                      ((nb095_alpha_dummy_012 D R S_cls E),
                                        (nb095_alpha_dummy_015 f)),
                                      ((nb095_alpha_dummy_011 D R S_cls E),
                                        (nb095_alpha_dummy_014 f)),
                                      ((nb095_alpha_dummy_017 D R S_cls E),
                                        (nb095_alpha_dummy_018 f)),
                                      ((nb095_alpha_dummy_001 D R S_cls E), u),
                                      ((nb095_alpha_dummy_002 D R S_cls E), x),
                                      ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
          [((nb095_alpha_dummy_201 D R S_cls E), (nb095_alpha_dummy_202 f)),
            ((nb095_alpha_dummy_170 D R S_cls E), (nb095_alpha_dummy_172 f)),
            ((nb095_alpha_dummy_169 D R S_cls E), (nb095_alpha_dummy_171 f)),
            ((nb095_alpha_dummy_199 D R S_cls E), (nb095_alpha_dummy_200 f)),
            ((nb095_alpha_dummy_173 D R S_cls E), (nb095_alpha_dummy_174 f)),
            ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
            ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
            ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
            ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
            ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
            ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_ccompl (syn_csn (syn_c0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))

@[expose]
noncomputable def nb095_split_alpha_0021 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_210 D R S_cls E), (nb095_alpha_dummy_212 f)),
        ((nb095_alpha_dummy_209 D R S_cls E), (nb095_alpha_dummy_211 f)),
        ((nb095_alpha_dummy_239 D R S_cls E), (nb095_alpha_dummy_240 f)),
        ((nb095_alpha_dummy_213 D R S_cls E), (nb095_alpha_dummy_214 f)),
        ((nb095_alpha_dummy_206 D R S_cls E), (nb095_alpha_dummy_208 f)),
        ((nb095_alpha_dummy_205 D R S_cls E), (nb095_alpha_dummy_207 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_210 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_205 D R S_cls E))) (Wff.neg
          (Wff.classEq (Class.cv (nb095_alpha_dummy_209 D R S_cls E))
            (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_210 D R S_cls E)))
              (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_212 f))
          (Class.cv (nb095_alpha_dummy_207 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb095_alpha_dummy_211 f))
            (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_212 f))) (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there
          (show (nb095_alpha_dummy_205 D R S_cls E) ≠ (nb095_alpha_dummy_210 D R S_cls E) from
            (by
              unfold nb095_alpha_dummy_210;
              with_reducible
                exact
                  (Nat.ne_of_lt
                    (mem_lt_freshVar (nb095_support_mem_0238 D R S_cls E) 1))))
          (show (nb095_alpha_dummy_207 f) ≠ (nb095_alpha_dummy_212 f) from (by
              unfold nb095_alpha_dummy_212;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0240 f) 1))))
          (TAlphaVar.there (show
              (nb095_alpha_dummy_205 D R S_cls E) ≠ (nb095_alpha_dummy_209 D R S_cls E) from (by
                unfold nb095_alpha_dummy_209;
                with_reducible
                  exact
                    (Nat.ne_of_lt
                      (mem_lt_freshVar (nb095_support_mem_0238 D R S_cls E) 0))))
            (show (nb095_alpha_dummy_207 f) ≠ (nb095_alpha_dummy_211 f) from (by
                unfold nb095_alpha_dummy_211;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0240 f) 0))))
            (TAlphaVar.there (show
                (nb095_alpha_dummy_205 D R S_cls E) ≠ (nb095_alpha_dummy_239 D R S_cls E) from
                (by
                  unfold nb095_alpha_dummy_239;
                  with_reducible
                    exact
                      (Nat.ne_of_lt
                        (mem_lt_freshVar (nb095_support_mem_0242 D R S_cls E) 0))))
              (show (nb095_alpha_dummy_207 f) ≠ (nb095_alpha_dummy_240 f) from (by
                  unfold nb095_alpha_dummy_240;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0243 f) 0))))
              (TAlphaVar.there (show (nb095_alpha_dummy_205 D R S_cls E) ≠
                    (nb095_alpha_dummy_213 D R S_cls E) from (by
                    unfold nb095_alpha_dummy_213;
                    with_reducible
                      exact
                        (Nat.ne_of_lt
                          (mem_lt_freshVar (nb095_support_mem_0239 D R S_cls E) 0))))
                (show (nb095_alpha_dummy_207 f) ≠ (nb095_alpha_dummy_214 f) from (by
                    unfold nb095_alpha_dummy_214;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0241 f) 0))))
                (TAlphaVar.there (freshVar_injective
                    (((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv ∪
                      ((syn_cvv)).fv) (by decide))
                  (freshVar_injective (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv)
                    (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb095_alpha_dummy_206 D R S_cls E))).fv ∪
                ((Class.cv (nb095_alpha_dummy_205 D R S_cls E))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb095_alpha_dummy_208 f))).fv ∪
                ((Class.cv (nb095_alpha_dummy_207 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_210 D R S_cls E) ≠
                                        (nb095_alpha_dummy_217 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_217;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0216 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_212 f) ≠ (nb095_alpha_dummy_219 f) from
                                      (by
                                        unfold nb095_alpha_dummy_219;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0217 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb095_alpha_dummy_210 D R S_cls E) ≠
        (nb095_alpha_dummy_218 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_218;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0216 D R S_cls E)
                                                  1)))) (show (nb095_alpha_dummy_212 f) ≠
        (nb095_alpha_dummy_220 f) from (by
                                          unfold nb095_alpha_dummy_220;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0217 f) 1))))
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_210 D R S_cls E) ≠ (nb095_alpha_dummy_243 D R S_cls E) from (by
          unfold nb095_alpha_dummy_243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0246 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_212 f) ≠ (nb095_alpha_dummy_244 f) from (by
          unfold nb095_alpha_dummy_244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0247 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_210 D R S_cls E) ≠ (nb095_alpha_dummy_241 D R S_cls E) from (by
          unfold nb095_alpha_dummy_241;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0244 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_212 f) ≠ (nb095_alpha_dummy_242 f) from (by
          unfold nb095_alpha_dummy_242;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0245 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_210 D R S_cls E))).fv) (by decide)) (freshVar_injective
                                      (((Class.cv (nb095_alpha_dummy_212 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_217 D R S_cls E) ≠
        (nb095_alpha_dummy_224 D R S_cls E) from (by
          unfold nb095_alpha_dummy_224;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0220
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_219 f) ≠ (nb095_alpha_dummy_227 f) from (by
          unfold nb095_alpha_dummy_227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0221
                    f)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_217 D R S_cls E) ≠
        (nb095_alpha_dummy_223 D R S_cls E) from (by
          unfold nb095_alpha_dummy_223;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0220
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_219 f) ≠ (nb095_alpha_dummy_226 f) from (by
          unfold nb095_alpha_dummy_226;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0221
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_217 D R S_cls E) ≠
        (nb095_alpha_dummy_221 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0218
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_219 f) ≠ (nb095_alpha_dummy_222 f) from (by
          unfold
            nb095_alpha_dummy_222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0219
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_225 D R S_cls E), (nb095_alpha_dummy_228 f)),
        ((nb095_alpha_dummy_224 D R S_cls E), (nb095_alpha_dummy_227 f)),
        ((nb095_alpha_dummy_223 D R S_cls E), (nb095_alpha_dummy_226 f)),
        ((nb095_alpha_dummy_221 D R S_cls E), (nb095_alpha_dummy_222 f)),
        ((nb095_alpha_dummy_217 D R S_cls E), (nb095_alpha_dummy_219 f)),
        ((nb095_alpha_dummy_218 D R S_cls E), (nb095_alpha_dummy_220 f)),
        ((nb095_alpha_dummy_243 D R S_cls E), (nb095_alpha_dummy_244 f)),
        ((nb095_alpha_dummy_241 D R S_cls E), (nb095_alpha_dummy_242 f)),
        ((nb095_alpha_dummy_210 D R S_cls E), (nb095_alpha_dummy_212 f)),
        ((nb095_alpha_dummy_209 D R S_cls E), (nb095_alpha_dummy_211 f)),
        ((nb095_alpha_dummy_239 D R S_cls E), (nb095_alpha_dummy_240 f)),
        ((nb095_alpha_dummy_213 D R S_cls E), (nb095_alpha_dummy_214 f)),
        ((nb095_alpha_dummy_206 D R S_cls E), (nb095_alpha_dummy_208 f)),
        ((nb095_alpha_dummy_205 D R S_cls E), (nb095_alpha_dummy_207 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_224 D R S_cls E) ≠
        (nb095_alpha_dummy_231 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0224
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_227 f) ≠ (nb095_alpha_dummy_232 f) from (by
          unfold
            nb095_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0225
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_224 D R S_cls E) ≠
        (nb095_alpha_dummy_229 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0222
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_227 f) ≠ (nb095_alpha_dummy_230 f) from (by
          unfold
            nb095_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0223
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_217
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_219 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_225
        D R S_cls E) ≠ (nb095_alpha_dummy_231 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0228
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_228 f) ≠ (nb095_alpha_dummy_232 f) from (by
          unfold
            nb095_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0229
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_225 D R S_cls E) ≠
        (nb095_alpha_dummy_229 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0226
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_228 f) ≠ (nb095_alpha_dummy_230 f) from (by
          unfold
            nb095_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0227
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_224 D R S_cls E) ≠ (nb095_alpha_dummy_231 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0224
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_227 f) ≠ (nb095_alpha_dummy_232 f) from (by
          unfold
            nb095_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0225
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_224 D R S_cls E) ≠
        (nb095_alpha_dummy_229 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0222
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_227 f) ≠ (nb095_alpha_dummy_230 f) from (by
          unfold
            nb095_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0223
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_217
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_219 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_225
        D R S_cls E) ≠ (nb095_alpha_dummy_231 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0228
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_228 f) ≠ (nb095_alpha_dummy_232 f) from (by
          unfold
            nb095_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0229
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_225 D R S_cls E) ≠
        (nb095_alpha_dummy_229 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0226
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_228 f) ≠ (nb095_alpha_dummy_230 f) from (by
          unfold
            nb095_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0227
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_225 D R S_cls E), (nb095_alpha_dummy_228 f)),
        ((nb095_alpha_dummy_224 D R S_cls E), (nb095_alpha_dummy_227 f)),
        ((nb095_alpha_dummy_223 D R S_cls E), (nb095_alpha_dummy_226 f)),
        ((nb095_alpha_dummy_221 D R S_cls E), (nb095_alpha_dummy_222 f)),
        ((nb095_alpha_dummy_217 D R S_cls E), (nb095_alpha_dummy_219 f)),
        ((nb095_alpha_dummy_218 D R S_cls E), (nb095_alpha_dummy_220 f)),
        ((nb095_alpha_dummy_243 D R S_cls E), (nb095_alpha_dummy_244 f)),
        ((nb095_alpha_dummy_241 D R S_cls E), (nb095_alpha_dummy_242 f)),
        ((nb095_alpha_dummy_210 D R S_cls E), (nb095_alpha_dummy_212 f)),
        ((nb095_alpha_dummy_209 D R S_cls E), (nb095_alpha_dummy_211 f)),
        ((nb095_alpha_dummy_239 D R S_cls E), (nb095_alpha_dummy_240 f)),
        ((nb095_alpha_dummy_213 D R S_cls E), (nb095_alpha_dummy_214 f)),
        ((nb095_alpha_dummy_206 D R S_cls E), (nb095_alpha_dummy_208 f)),
        ((nb095_alpha_dummy_205 D R S_cls E), (nb095_alpha_dummy_207 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_217 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_219 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_217
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_219 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_224 D R S_cls E) ≠ (nb095_alpha_dummy_235 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0232
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_227 f) ≠ (nb095_alpha_dummy_236 f) from (by
          unfold
            nb095_alpha_dummy_236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0233
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_224 D R S_cls E) ≠
        (nb095_alpha_dummy_233 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0230
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_227 f) ≠ (nb095_alpha_dummy_234 f) from (by
          unfold
            nb095_alpha_dummy_234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0231
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_217
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_219 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_224
        D R S_cls E) ≠ (nb095_alpha_dummy_235 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0232
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_227 f) ≠ (nb095_alpha_dummy_236 f) from (by
          unfold
            nb095_alpha_dummy_236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0233
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_224 D R S_cls E) ≠
        (nb095_alpha_dummy_233 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0230
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_227 f) ≠ (nb095_alpha_dummy_234 f) from (by
          unfold
            nb095_alpha_dummy_234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0231
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_217
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_219 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_225 D R S_cls E) ≠ (nb095_alpha_dummy_237 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_237;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0236
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_228 f) ≠ (nb095_alpha_dummy_238 f) from (by
          unfold
            nb095_alpha_dummy_238;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0237
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_225 D R S_cls E) ≠
        (nb095_alpha_dummy_233 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0234
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_228 f) ≠ (nb095_alpha_dummy_234 f) from (by
          unfold
            nb095_alpha_dummy_234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0235
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_225
        D R S_cls E) ≠ (nb095_alpha_dummy_237 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_237;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0236
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_228 f) ≠ (nb095_alpha_dummy_238 f) from (by
          unfold
            nb095_alpha_dummy_238;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0237
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_225 D R S_cls E) ≠
        (nb095_alpha_dummy_233 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0234
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_228 f) ≠ (nb095_alpha_dummy_234 f) from (by
          unfold
            nb095_alpha_dummy_234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0235
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_217 D R S_cls E) ≠
        (nb095_alpha_dummy_221 D R S_cls E) from (by
          unfold nb095_alpha_dummy_221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0218 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_219 f) ≠ (nb095_alpha_dummy_222 f) from (by
          unfold nb095_alpha_dummy_222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_221 D R S_cls E),
        (nb095_alpha_dummy_222 f)), ((nb095_alpha_dummy_217 D R S_cls E),
        (nb095_alpha_dummy_219 f)), ((nb095_alpha_dummy_218 D R S_cls E),
        (nb095_alpha_dummy_220 f)), ((nb095_alpha_dummy_243 D R S_cls E),
        (nb095_alpha_dummy_244 f)), ((nb095_alpha_dummy_241 D R S_cls E),
        (nb095_alpha_dummy_242 f)), ((nb095_alpha_dummy_210 D R S_cls E),
        (nb095_alpha_dummy_212 f)), ((nb095_alpha_dummy_209 D R S_cls E),
        (nb095_alpha_dummy_211 f)), ((nb095_alpha_dummy_239 D R S_cls E),
        (nb095_alpha_dummy_240 f)), ((nb095_alpha_dummy_213 D R S_cls E),
        (nb095_alpha_dummy_214 f)), ((nb095_alpha_dummy_206 D R S_cls E),
        (nb095_alpha_dummy_208 f)), ((nb095_alpha_dummy_205 D R S_cls E),
        (nb095_alpha_dummy_207 f)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_217 D R S_cls E) ≠
        (nb095_alpha_dummy_221 D R S_cls E) from (by
          unfold nb095_alpha_dummy_221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0218 D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_219 f) ≠ (nb095_alpha_dummy_222 f) from (by
          unfold nb095_alpha_dummy_222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb095_alpha_dummy_217 D R S_cls E) ≠ (nb095_alpha_dummy_221 D R S_cls E) from (by
          unfold nb095_alpha_dummy_221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0218 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_219 f) ≠ (nb095_alpha_dummy_222 f) from (by
          unfold nb095_alpha_dummy_222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_221 D R S_cls E),
        (nb095_alpha_dummy_222 f)), ((nb095_alpha_dummy_217 D R S_cls E),
        (nb095_alpha_dummy_219 f)), ((nb095_alpha_dummy_218 D R S_cls E),
        (nb095_alpha_dummy_220 f)), ((nb095_alpha_dummy_243 D R S_cls E),
        (nb095_alpha_dummy_244 f)), ((nb095_alpha_dummy_241 D R S_cls E),
        (nb095_alpha_dummy_242 f)), ((nb095_alpha_dummy_210 D R S_cls E),
        (nb095_alpha_dummy_212 f)), ((nb095_alpha_dummy_209 D R S_cls E),
        (nb095_alpha_dummy_211 f)), ((nb095_alpha_dummy_239 D R S_cls E),
        (nb095_alpha_dummy_240 f)), ((nb095_alpha_dummy_213 D R S_cls E),
        (nb095_alpha_dummy_214 f)), ((nb095_alpha_dummy_206 D R S_cls E),
        (nb095_alpha_dummy_208 f)), ((nb095_alpha_dummy_205 D R S_cls E),
        (nb095_alpha_dummy_207 f)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_210 D R S_cls E) ≠
                                        (nb095_alpha_dummy_217 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_217;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0216 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_212 f) ≠ (nb095_alpha_dummy_219 f) from
                                      (by
                                        unfold nb095_alpha_dummy_219;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0217 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb095_alpha_dummy_210 D R S_cls E) ≠
        (nb095_alpha_dummy_218 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_218;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0216 D R S_cls E)
                                                  1)))) (show (nb095_alpha_dummy_212 f) ≠
        (nb095_alpha_dummy_220 f) from (by
                                          unfold nb095_alpha_dummy_220;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0217 f) 1))))
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_210 D R S_cls E) ≠ (nb095_alpha_dummy_243 D R S_cls E) from (by
          unfold nb095_alpha_dummy_243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0246 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_212 f) ≠ (nb095_alpha_dummy_244 f) from (by
          unfold nb095_alpha_dummy_244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0247 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_210 D R S_cls E) ≠ (nb095_alpha_dummy_241 D R S_cls E) from (by
          unfold nb095_alpha_dummy_241;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0244 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_212 f) ≠ (nb095_alpha_dummy_242 f) from (by
          unfold nb095_alpha_dummy_242;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0245 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_210 D R S_cls E))).fv) (by decide)) (freshVar_injective
                                      (((Class.cv (nb095_alpha_dummy_212 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_217 D R S_cls E) ≠
        (nb095_alpha_dummy_224 D R S_cls E) from (by
          unfold nb095_alpha_dummy_224;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0220
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_219 f) ≠ (nb095_alpha_dummy_227 f) from (by
          unfold nb095_alpha_dummy_227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0221
                    f)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_217 D R S_cls E) ≠
        (nb095_alpha_dummy_223 D R S_cls E) from (by
          unfold nb095_alpha_dummy_223;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0220
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_219 f) ≠ (nb095_alpha_dummy_226 f) from (by
          unfold nb095_alpha_dummy_226;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0221
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_217 D R S_cls E) ≠
        (nb095_alpha_dummy_221 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0218
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_219 f) ≠ (nb095_alpha_dummy_222 f) from (by
          unfold
            nb095_alpha_dummy_222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0219
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_225 D R S_cls E), (nb095_alpha_dummy_228 f)),
        ((nb095_alpha_dummy_224 D R S_cls E), (nb095_alpha_dummy_227 f)),
        ((nb095_alpha_dummy_223 D R S_cls E), (nb095_alpha_dummy_226 f)),
        ((nb095_alpha_dummy_221 D R S_cls E), (nb095_alpha_dummy_222 f)),
        ((nb095_alpha_dummy_217 D R S_cls E), (nb095_alpha_dummy_219 f)),
        ((nb095_alpha_dummy_218 D R S_cls E), (nb095_alpha_dummy_220 f)),
        ((nb095_alpha_dummy_243 D R S_cls E), (nb095_alpha_dummy_244 f)),
        ((nb095_alpha_dummy_241 D R S_cls E), (nb095_alpha_dummy_242 f)),
        ((nb095_alpha_dummy_210 D R S_cls E), (nb095_alpha_dummy_212 f)),
        ((nb095_alpha_dummy_209 D R S_cls E), (nb095_alpha_dummy_211 f)),
        ((nb095_alpha_dummy_239 D R S_cls E), (nb095_alpha_dummy_240 f)),
        ((nb095_alpha_dummy_213 D R S_cls E), (nb095_alpha_dummy_214 f)),
        ((nb095_alpha_dummy_206 D R S_cls E), (nb095_alpha_dummy_208 f)),
        ((nb095_alpha_dummy_205 D R S_cls E), (nb095_alpha_dummy_207 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_224 D R S_cls E) ≠
        (nb095_alpha_dummy_231 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0224
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_227 f) ≠ (nb095_alpha_dummy_232 f) from (by
          unfold
            nb095_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0225
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_224 D R S_cls E) ≠
        (nb095_alpha_dummy_229 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0222
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_227 f) ≠ (nb095_alpha_dummy_230 f) from (by
          unfold
            nb095_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0223
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_217
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_219 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_225
        D R S_cls E) ≠ (nb095_alpha_dummy_231 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0228
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_228 f) ≠ (nb095_alpha_dummy_232 f) from (by
          unfold
            nb095_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0229
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_225 D R S_cls E) ≠
        (nb095_alpha_dummy_229 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0226
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_228 f) ≠ (nb095_alpha_dummy_230 f) from (by
          unfold
            nb095_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0227
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_224 D R S_cls E) ≠ (nb095_alpha_dummy_231 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0224
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_227 f) ≠ (nb095_alpha_dummy_232 f) from (by
          unfold
            nb095_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0225
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_224 D R S_cls E) ≠
        (nb095_alpha_dummy_229 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0222
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_227 f) ≠ (nb095_alpha_dummy_230 f) from (by
          unfold
            nb095_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0223
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_217
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_219 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_225
        D R S_cls E) ≠ (nb095_alpha_dummy_231 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0228
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_228 f) ≠ (nb095_alpha_dummy_232 f) from (by
          unfold
            nb095_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0229
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_225 D R S_cls E) ≠
        (nb095_alpha_dummy_229 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0226
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_228 f) ≠ (nb095_alpha_dummy_230 f) from (by
          unfold
            nb095_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0227
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_225 D R S_cls E), (nb095_alpha_dummy_228 f)),
        ((nb095_alpha_dummy_224 D R S_cls E), (nb095_alpha_dummy_227 f)),
        ((nb095_alpha_dummy_223 D R S_cls E), (nb095_alpha_dummy_226 f)),
        ((nb095_alpha_dummy_221 D R S_cls E), (nb095_alpha_dummy_222 f)),
        ((nb095_alpha_dummy_217 D R S_cls E), (nb095_alpha_dummy_219 f)),
        ((nb095_alpha_dummy_218 D R S_cls E), (nb095_alpha_dummy_220 f)),
        ((nb095_alpha_dummy_243 D R S_cls E), (nb095_alpha_dummy_244 f)),
        ((nb095_alpha_dummy_241 D R S_cls E), (nb095_alpha_dummy_242 f)),
        ((nb095_alpha_dummy_210 D R S_cls E), (nb095_alpha_dummy_212 f)),
        ((nb095_alpha_dummy_209 D R S_cls E), (nb095_alpha_dummy_211 f)),
        ((nb095_alpha_dummy_239 D R S_cls E), (nb095_alpha_dummy_240 f)),
        ((nb095_alpha_dummy_213 D R S_cls E), (nb095_alpha_dummy_214 f)),
        ((nb095_alpha_dummy_206 D R S_cls E), (nb095_alpha_dummy_208 f)),
        ((nb095_alpha_dummy_205 D R S_cls E), (nb095_alpha_dummy_207 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_217 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_219 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_217
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_219 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_224 D R S_cls E) ≠ (nb095_alpha_dummy_235 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0232
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_227 f) ≠ (nb095_alpha_dummy_236 f) from (by
          unfold
            nb095_alpha_dummy_236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0233
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_224 D R S_cls E) ≠
        (nb095_alpha_dummy_233 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0230
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_227 f) ≠ (nb095_alpha_dummy_234 f) from (by
          unfold
            nb095_alpha_dummy_234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0231
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_217
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_219 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_224
        D R S_cls E) ≠ (nb095_alpha_dummy_235 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0232
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_227 f) ≠ (nb095_alpha_dummy_236 f) from (by
          unfold
            nb095_alpha_dummy_236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0233
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_224 D R S_cls E) ≠
        (nb095_alpha_dummy_233 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0230
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_227 f) ≠ (nb095_alpha_dummy_234 f) from (by
          unfold
            nb095_alpha_dummy_234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0231
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_217
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_219 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_225 D R S_cls E) ≠ (nb095_alpha_dummy_237 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_237;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0236
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_228 f) ≠ (nb095_alpha_dummy_238 f) from (by
          unfold
            nb095_alpha_dummy_238;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0237
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_225 D R S_cls E) ≠
        (nb095_alpha_dummy_233 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0234
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_228 f) ≠ (nb095_alpha_dummy_234 f) from (by
          unfold
            nb095_alpha_dummy_234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0235
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_225
        D R S_cls E) ≠ (nb095_alpha_dummy_237 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_237;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0236
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_228 f) ≠ (nb095_alpha_dummy_238 f) from (by
          unfold
            nb095_alpha_dummy_238;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0237
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_225 D R S_cls E) ≠
        (nb095_alpha_dummy_233 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0234
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_228 f) ≠ (nb095_alpha_dummy_234 f) from (by
          unfold
            nb095_alpha_dummy_234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0235
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_217 D R S_cls E) ≠
        (nb095_alpha_dummy_221 D R S_cls E) from (by
          unfold nb095_alpha_dummy_221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0218 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_219 f) ≠ (nb095_alpha_dummy_222 f) from (by
          unfold nb095_alpha_dummy_222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_221 D R S_cls E),
        (nb095_alpha_dummy_222 f)), ((nb095_alpha_dummy_217 D R S_cls E),
        (nb095_alpha_dummy_219 f)), ((nb095_alpha_dummy_218 D R S_cls E),
        (nb095_alpha_dummy_220 f)), ((nb095_alpha_dummy_243 D R S_cls E),
        (nb095_alpha_dummy_244 f)), ((nb095_alpha_dummy_241 D R S_cls E),
        (nb095_alpha_dummy_242 f)), ((nb095_alpha_dummy_210 D R S_cls E),
        (nb095_alpha_dummy_212 f)), ((nb095_alpha_dummy_209 D R S_cls E),
        (nb095_alpha_dummy_211 f)), ((nb095_alpha_dummy_239 D R S_cls E),
        (nb095_alpha_dummy_240 f)), ((nb095_alpha_dummy_213 D R S_cls E),
        (nb095_alpha_dummy_214 f)), ((nb095_alpha_dummy_206 D R S_cls E),
        (nb095_alpha_dummy_208 f)), ((nb095_alpha_dummy_205 D R S_cls E),
        (nb095_alpha_dummy_207 f)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_217 D R S_cls E) ≠
        (nb095_alpha_dummy_221 D R S_cls E) from (by
          unfold nb095_alpha_dummy_221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0218 D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_219 f) ≠ (nb095_alpha_dummy_222 f) from (by
          unfold nb095_alpha_dummy_222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb095_alpha_dummy_217 D R S_cls E) ≠ (nb095_alpha_dummy_221 D R S_cls E) from (by
          unfold nb095_alpha_dummy_221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0218 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_219 f) ≠ (nb095_alpha_dummy_222 f) from (by
          unfold nb095_alpha_dummy_222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_221 D R S_cls E),
        (nb095_alpha_dummy_222 f)), ((nb095_alpha_dummy_217 D R S_cls E),
        (nb095_alpha_dummy_219 f)), ((nb095_alpha_dummy_218 D R S_cls E),
        (nb095_alpha_dummy_220 f)), ((nb095_alpha_dummy_243 D R S_cls E),
        (nb095_alpha_dummy_244 f)), ((nb095_alpha_dummy_241 D R S_cls E),
        (nb095_alpha_dummy_242 f)), ((nb095_alpha_dummy_210 D R S_cls E),
        (nb095_alpha_dummy_212 f)), ((nb095_alpha_dummy_209 D R S_cls E),
        (nb095_alpha_dummy_211 f)), ((nb095_alpha_dummy_239 D R S_cls E),
        (nb095_alpha_dummy_240 f)), ((nb095_alpha_dummy_213 D R S_cls E),
        (nb095_alpha_dummy_214 f)), ((nb095_alpha_dummy_206 D R S_cls E),
        (nb095_alpha_dummy_208 f)), ((nb095_alpha_dummy_205 D R S_cls E),
        (nb095_alpha_dummy_207 f)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb095_alpha_dummy_241 D R S_cls E), (nb095_alpha_dummy_242 f)),
                    ((nb095_alpha_dummy_210 D R S_cls E), (nb095_alpha_dummy_212 f)),
                    ((nb095_alpha_dummy_209 D R S_cls E), (nb095_alpha_dummy_211 f)),
                    ((nb095_alpha_dummy_239 D R S_cls E), (nb095_alpha_dummy_240 f)),
                    ((nb095_alpha_dummy_213 D R S_cls E), (nb095_alpha_dummy_214 f)),
                    ((nb095_alpha_dummy_206 D R S_cls E), (nb095_alpha_dummy_208 f)),
                    ((nb095_alpha_dummy_205 D R S_cls E), (nb095_alpha_dummy_207 f)),
                    ((nb095_alpha_dummy_001 D R S_cls E), u),
                    ((nb095_alpha_dummy_002 D R S_cls E), x),
                    ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_ccompl (syn_csn (syn_c0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired


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
noncomputable def nb095_split_alpha_0022 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_213 D R S_cls E), (nb095_alpha_dummy_214 f)),
        ((nb095_alpha_dummy_206 D R S_cls E), (nb095_alpha_dummy_208 f)),
        ((nb095_alpha_dummy_205 D R S_cls E), (nb095_alpha_dummy_207 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_213 D R S_cls E)) (syn_ccompl
            (Class.cab (nb095_alpha_dummy_209 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_210 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_206 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_209 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_210 D R S_cls E)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_213 D R S_cls E)) (syn_ccompl
              (Class.cab (nb095_alpha_dummy_209 D R S_cls E)
                (syn_wrex (nb095_alpha_dummy_210 D R S_cls E)
                  (Class.cv (nb095_alpha_dummy_205 D R S_cls E))
                  (Wff.classEq (Class.cv (nb095_alpha_dummy_209 D R S_cls E))
                    (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_210 D R S_cls E)))
                      (syn_csn (syn_c0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_214 f)) (syn_ccompl
            (Class.cab (nb095_alpha_dummy_211 f)
              (syn_wrex (nb095_alpha_dummy_212 f) (Class.cv (nb095_alpha_dummy_208 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_211 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_212 f)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_214 f)) (syn_ccompl
              (Class.cab (nb095_alpha_dummy_211 f)
                (syn_wrex (nb095_alpha_dummy_212 f) (Class.cv (nb095_alpha_dummy_207 f))
                  (Wff.classEq (Class.cv (nb095_alpha_dummy_211 f))
                    (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_212 f)))
                      (syn_csn (syn_c0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095_alpha_dummy_206 D R S_cls E) ≠
                              (nb095_alpha_dummy_210 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_210;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0210 D R S_cls E)
                                      1))))
                          (show (nb095_alpha_dummy_208 f) ≠ (nb095_alpha_dummy_212 f) from (by
                              unfold nb095_alpha_dummy_212;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0212 f) 1))))
                          (TAlphaVar.there (show (nb095_alpha_dummy_206 D R S_cls E) ≠
                                (nb095_alpha_dummy_209 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_209;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0210 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_208 f) ≠ (nb095_alpha_dummy_211 f) from (by
                                unfold nb095_alpha_dummy_211;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0212 f) 0))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_206 D R S_cls E) ≠
                                  (nb095_alpha_dummy_215 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_215;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0214 D R S_cls E) 0))))
                              (show (nb095_alpha_dummy_208 f) ≠ (nb095_alpha_dummy_216 f) from
                                (by
                                  unfold nb095_alpha_dummy_216;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0215 f) 0))))
                              (TAlphaVar.there (show (nb095_alpha_dummy_206 D R S_cls E) ≠
                                    (nb095_alpha_dummy_213 D R S_cls E) from (by
                                    unfold nb095_alpha_dummy_213;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0211 D R S_cls E) 0)))) (show
                                  (nb095_alpha_dummy_208 f) ≠ (nb095_alpha_dummy_214 f) from (by
                                    unfold nb095_alpha_dummy_214;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0213 f)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095_alpha_dummy_206 D R S_cls E))).fv ∪
                              ((Class.cv (nb095_alpha_dummy_205 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb095_alpha_dummy_208 f))).fv ∪
                              ((Class.cv (nb095_alpha_dummy_207 f))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095_alpha_dummy_210 D R S_cls E) ≠
                                      (nb095_alpha_dummy_217 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_217;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0216 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_212 f) ≠ (nb095_alpha_dummy_219 f) from
                                    (by
                                      unfold nb095_alpha_dummy_219;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0217 f)
                                              0)))) (TAlphaVar.there (show
                                      (nb095_alpha_dummy_210 D R S_cls E) ≠
                                        (nb095_alpha_dummy_218 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_218;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0216 D R S_cls E) 1)))) (show
                                      (nb095_alpha_dummy_212 f) ≠ (nb095_alpha_dummy_220 f) from
                                      (by
                                        unfold nb095_alpha_dummy_220;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0217 f)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb095_alpha_dummy_210 D R S_cls E))).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv (nb095_alpha_dummy_212 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_217 D R S_cls E) ≠ (nb095_alpha_dummy_224 D R S_cls E) from (by
          unfold nb095_alpha_dummy_224;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0220 D
                    R S_cls E)
                  1)))) (show (nb095_alpha_dummy_219 f) ≠ (nb095_alpha_dummy_227 f) from (by
          unfold nb095_alpha_dummy_227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0221 f)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_217 D R S_cls E) ≠
        (nb095_alpha_dummy_223 D R S_cls E) from (by
          unfold nb095_alpha_dummy_223;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0220
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_219 f) ≠ (nb095_alpha_dummy_226 f) from (by
          unfold nb095_alpha_dummy_226;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0221
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_217 D R S_cls E) ≠
        (nb095_alpha_dummy_221 D R S_cls E) from (by
          unfold nb095_alpha_dummy_221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0218
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_219 f) ≠ (nb095_alpha_dummy_222 f) from (by
          unfold nb095_alpha_dummy_222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0219
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_225 D R S_cls E), (nb095_alpha_dummy_228 f)),
        ((nb095_alpha_dummy_224 D R S_cls E), (nb095_alpha_dummy_227 f)),
        ((nb095_alpha_dummy_223 D R S_cls E), (nb095_alpha_dummy_226 f)),
        ((nb095_alpha_dummy_221 D R S_cls E), (nb095_alpha_dummy_222 f)),
        ((nb095_alpha_dummy_217 D R S_cls E), (nb095_alpha_dummy_219 f)),
        ((nb095_alpha_dummy_218 D R S_cls E), (nb095_alpha_dummy_220 f)),
        ((nb095_alpha_dummy_210 D R S_cls E), (nb095_alpha_dummy_212 f)),
        ((nb095_alpha_dummy_209 D R S_cls E), (nb095_alpha_dummy_211 f)),
        ((nb095_alpha_dummy_215 D R S_cls E), (nb095_alpha_dummy_216 f)),
        ((nb095_alpha_dummy_213 D R S_cls E), (nb095_alpha_dummy_214 f)),
        ((nb095_alpha_dummy_206 D R S_cls E), (nb095_alpha_dummy_208 f)),
        ((nb095_alpha_dummy_205 D R S_cls E), (nb095_alpha_dummy_207 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_224 D R S_cls E) ≠
        (nb095_alpha_dummy_231 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0224
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_227 f) ≠ (nb095_alpha_dummy_232 f) from (by
          unfold
            nb095_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0225
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_224 D R S_cls E) ≠
        (nb095_alpha_dummy_229 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0222
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_227 f) ≠ (nb095_alpha_dummy_230 f) from (by
          unfold
            nb095_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0223
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_217
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_219 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_225
        D R S_cls E) ≠ (nb095_alpha_dummy_231 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0228
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_228 f) ≠ (nb095_alpha_dummy_232 f) from (by
          unfold
            nb095_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0229
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_225 D R S_cls E) ≠
        (nb095_alpha_dummy_229 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0226
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_228 f) ≠ (nb095_alpha_dummy_230 f) from (by
          unfold
            nb095_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0227
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_224 D R S_cls E) ≠ (nb095_alpha_dummy_231
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0224
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_227 f) ≠ (nb095_alpha_dummy_232 f) from (by
          unfold
            nb095_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0225
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_224 D R S_cls E) ≠
        (nb095_alpha_dummy_229 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0222
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_227 f) ≠ (nb095_alpha_dummy_230 f) from (by
          unfold
            nb095_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0223
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_217
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_219 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_225
        D R S_cls E) ≠ (nb095_alpha_dummy_231 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0228
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_228 f) ≠ (nb095_alpha_dummy_232 f) from (by
          unfold
            nb095_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0229
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_225 D R S_cls E) ≠
        (nb095_alpha_dummy_229 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0226
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_228 f) ≠ (nb095_alpha_dummy_230 f) from (by
          unfold
            nb095_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0227
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_225 D R S_cls E), (nb095_alpha_dummy_228 f)),
        ((nb095_alpha_dummy_224 D R S_cls E), (nb095_alpha_dummy_227 f)),
        ((nb095_alpha_dummy_223 D R S_cls E), (nb095_alpha_dummy_226 f)),
        ((nb095_alpha_dummy_221 D R S_cls E), (nb095_alpha_dummy_222 f)),
        ((nb095_alpha_dummy_217 D R S_cls E), (nb095_alpha_dummy_219 f)),
        ((nb095_alpha_dummy_218 D R S_cls E), (nb095_alpha_dummy_220 f)),
        ((nb095_alpha_dummy_210 D R S_cls E), (nb095_alpha_dummy_212 f)),
        ((nb095_alpha_dummy_209 D R S_cls E), (nb095_alpha_dummy_211 f)),
        ((nb095_alpha_dummy_215 D R S_cls E), (nb095_alpha_dummy_216 f)),
        ((nb095_alpha_dummy_213 D R S_cls E), (nb095_alpha_dummy_214 f)),
        ((nb095_alpha_dummy_206 D R S_cls E), (nb095_alpha_dummy_208 f)),
        ((nb095_alpha_dummy_205 D R S_cls E), (nb095_alpha_dummy_207 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_217 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_219 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_217
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_219 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_224 D R S_cls E) ≠ (nb095_alpha_dummy_235
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0232
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_227 f) ≠ (nb095_alpha_dummy_236 f) from (by
          unfold
            nb095_alpha_dummy_236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0233
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_224 D R S_cls E) ≠
        (nb095_alpha_dummy_233 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0230
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_227 f) ≠ (nb095_alpha_dummy_234 f) from (by
          unfold
            nb095_alpha_dummy_234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0231
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_217
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_219 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_224
        D R S_cls E) ≠ (nb095_alpha_dummy_235 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0232
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_227 f) ≠ (nb095_alpha_dummy_236 f) from (by
          unfold
            nb095_alpha_dummy_236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0233
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_224 D R S_cls E) ≠
        (nb095_alpha_dummy_233 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0230
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_227 f) ≠ (nb095_alpha_dummy_234 f) from (by
          unfold
            nb095_alpha_dummy_234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0231
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_217
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_219 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_225 D R S_cls E) ≠ (nb095_alpha_dummy_237
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_237;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0236
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_228 f) ≠ (nb095_alpha_dummy_238 f) from (by
          unfold
            nb095_alpha_dummy_238;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0237
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_225 D R S_cls E) ≠
        (nb095_alpha_dummy_233 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0234
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_228 f) ≠ (nb095_alpha_dummy_234 f) from (by
          unfold
            nb095_alpha_dummy_234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0235
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_225
        D R S_cls E) ≠ (nb095_alpha_dummy_237 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_237;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0236
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_228 f) ≠ (nb095_alpha_dummy_238 f) from (by
          unfold
            nb095_alpha_dummy_238;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0237
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_225 D R S_cls E) ≠
        (nb095_alpha_dummy_233 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0234
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_228 f) ≠ (nb095_alpha_dummy_234 f) from (by
          unfold
            nb095_alpha_dummy_234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0235
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_217 D R S_cls E) ≠ (nb095_alpha_dummy_221 D R S_cls E) from (by
          unfold nb095_alpha_dummy_221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0218 D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_219 f) ≠ (nb095_alpha_dummy_222 f) from (by
          unfold nb095_alpha_dummy_222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_221 D R S_cls E), (nb095_alpha_dummy_222 f)),
        ((nb095_alpha_dummy_217 D R S_cls E), (nb095_alpha_dummy_219 f)),
        ((nb095_alpha_dummy_218 D R S_cls E), (nb095_alpha_dummy_220 f)),
        ((nb095_alpha_dummy_210 D R S_cls E), (nb095_alpha_dummy_212 f)),
        ((nb095_alpha_dummy_209 D R S_cls E), (nb095_alpha_dummy_211 f)),
        ((nb095_alpha_dummy_215 D R S_cls E), (nb095_alpha_dummy_216 f)),
        ((nb095_alpha_dummy_213 D R S_cls E), (nb095_alpha_dummy_214 f)),
        ((nb095_alpha_dummy_206 D R S_cls E), (nb095_alpha_dummy_208 f)),
        ((nb095_alpha_dummy_205 D R S_cls E), (nb095_alpha_dummy_207 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show
        (nb095_alpha_dummy_217 D R S_cls E) ≠ (nb095_alpha_dummy_221 D R S_cls E) from (by
          unfold nb095_alpha_dummy_221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0218 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_219 f) ≠ (nb095_alpha_dummy_222 f) from (by
          unfold nb095_alpha_dummy_222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_217 D R S_cls E) ≠ (nb095_alpha_dummy_221 D R S_cls E) from (by
          unfold nb095_alpha_dummy_221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0218 D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_219 f) ≠ (nb095_alpha_dummy_222 f) from (by
          unfold nb095_alpha_dummy_222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_221 D R S_cls E), (nb095_alpha_dummy_222 f)),
        ((nb095_alpha_dummy_217 D R S_cls E), (nb095_alpha_dummy_219 f)),
        ((nb095_alpha_dummy_218 D R S_cls E), (nb095_alpha_dummy_220 f)),
        ((nb095_alpha_dummy_210 D R S_cls E), (nb095_alpha_dummy_212 f)),
        ((nb095_alpha_dummy_209 D R S_cls E), (nb095_alpha_dummy_211 f)),
        ((nb095_alpha_dummy_215 D R S_cls E), (nb095_alpha_dummy_216 f)),
        ((nb095_alpha_dummy_213 D R S_cls E), (nb095_alpha_dummy_214 f)),
        ((nb095_alpha_dummy_206 D R S_cls E), (nb095_alpha_dummy_208 f)),
        ((nb095_alpha_dummy_205 D R S_cls E), (nb095_alpha_dummy_207 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095_alpha_dummy_206 D R S_cls E) ≠
                              (nb095_alpha_dummy_210 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_210;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0210 D R S_cls E)
                                      1))))
                          (show (nb095_alpha_dummy_208 f) ≠ (nb095_alpha_dummy_212 f) from (by
                              unfold nb095_alpha_dummy_212;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0212 f) 1))))
                          (TAlphaVar.there (show (nb095_alpha_dummy_206 D R S_cls E) ≠
                                (nb095_alpha_dummy_209 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_209;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0210 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_208 f) ≠ (nb095_alpha_dummy_211 f) from (by
                                unfold nb095_alpha_dummy_211;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0212 f) 0))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_206 D R S_cls E) ≠
                                  (nb095_alpha_dummy_215 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_215;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0214 D R S_cls E) 0))))
                              (show (nb095_alpha_dummy_208 f) ≠ (nb095_alpha_dummy_216 f) from
                                (by
                                  unfold nb095_alpha_dummy_216;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0215 f) 0))))
                              (TAlphaVar.there (show (nb095_alpha_dummy_206 D R S_cls E) ≠
                                    (nb095_alpha_dummy_213 D R S_cls E) from (by
                                    unfold nb095_alpha_dummy_213;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0211 D R S_cls E) 0)))) (show
                                  (nb095_alpha_dummy_208 f) ≠ (nb095_alpha_dummy_214 f) from (by
                                    unfold nb095_alpha_dummy_214;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0213 f)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095_alpha_dummy_206 D R S_cls E))).fv ∪
                              ((Class.cv (nb095_alpha_dummy_205 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb095_alpha_dummy_208 f))).fv ∪
                              ((Class.cv (nb095_alpha_dummy_207 f))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095_alpha_dummy_210 D R S_cls E) ≠
                                      (nb095_alpha_dummy_217 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_217;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0216 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_212 f) ≠ (nb095_alpha_dummy_219 f) from
                                    (by
                                      unfold nb095_alpha_dummy_219;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0217 f)
                                              0)))) (TAlphaVar.there (show
                                      (nb095_alpha_dummy_210 D R S_cls E) ≠
                                        (nb095_alpha_dummy_218 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_218;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0216 D R S_cls E) 1)))) (show
                                      (nb095_alpha_dummy_212 f) ≠ (nb095_alpha_dummy_220 f) from
                                      (by
                                        unfold nb095_alpha_dummy_220;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0217 f)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb095_alpha_dummy_210 D R S_cls E))).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv (nb095_alpha_dummy_212 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_217 D R S_cls E) ≠ (nb095_alpha_dummy_224 D R S_cls E) from (by
          unfold nb095_alpha_dummy_224;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0220 D
                    R S_cls E)
                  1)))) (show (nb095_alpha_dummy_219 f) ≠ (nb095_alpha_dummy_227 f) from (by
          unfold nb095_alpha_dummy_227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0221 f)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_217 D R S_cls E) ≠
        (nb095_alpha_dummy_223 D R S_cls E) from (by
          unfold nb095_alpha_dummy_223;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0220
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_219 f) ≠ (nb095_alpha_dummy_226 f) from (by
          unfold nb095_alpha_dummy_226;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0221
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_217 D R S_cls E) ≠
        (nb095_alpha_dummy_221 D R S_cls E) from (by
          unfold nb095_alpha_dummy_221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0218
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_219 f) ≠ (nb095_alpha_dummy_222 f) from (by
          unfold nb095_alpha_dummy_222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0219
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_225 D R S_cls E), (nb095_alpha_dummy_228 f)),
        ((nb095_alpha_dummy_224 D R S_cls E), (nb095_alpha_dummy_227 f)),
        ((nb095_alpha_dummy_223 D R S_cls E), (nb095_alpha_dummy_226 f)),
        ((nb095_alpha_dummy_221 D R S_cls E), (nb095_alpha_dummy_222 f)),
        ((nb095_alpha_dummy_217 D R S_cls E), (nb095_alpha_dummy_219 f)),
        ((nb095_alpha_dummy_218 D R S_cls E), (nb095_alpha_dummy_220 f)),
        ((nb095_alpha_dummy_210 D R S_cls E), (nb095_alpha_dummy_212 f)),
        ((nb095_alpha_dummy_209 D R S_cls E), (nb095_alpha_dummy_211 f)),
        ((nb095_alpha_dummy_215 D R S_cls E), (nb095_alpha_dummy_216 f)),
        ((nb095_alpha_dummy_213 D R S_cls E), (nb095_alpha_dummy_214 f)),
        ((nb095_alpha_dummy_206 D R S_cls E), (nb095_alpha_dummy_208 f)),
        ((nb095_alpha_dummy_205 D R S_cls E), (nb095_alpha_dummy_207 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_224 D R S_cls E) ≠
        (nb095_alpha_dummy_231 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0224
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_227 f) ≠ (nb095_alpha_dummy_232 f) from (by
          unfold
            nb095_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0225
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_224 D R S_cls E) ≠
        (nb095_alpha_dummy_229 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0222
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_227 f) ≠ (nb095_alpha_dummy_230 f) from (by
          unfold
            nb095_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0223
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_217
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_219 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_225
        D R S_cls E) ≠ (nb095_alpha_dummy_231 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0228
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_228 f) ≠ (nb095_alpha_dummy_232 f) from (by
          unfold
            nb095_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0229
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_225 D R S_cls E) ≠
        (nb095_alpha_dummy_229 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0226
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_228 f) ≠ (nb095_alpha_dummy_230 f) from (by
          unfold
            nb095_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0227
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_224 D R S_cls E) ≠ (nb095_alpha_dummy_231
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0224
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_227 f) ≠ (nb095_alpha_dummy_232 f) from (by
          unfold
            nb095_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0225
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_224 D R S_cls E) ≠
        (nb095_alpha_dummy_229 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0222
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_227 f) ≠ (nb095_alpha_dummy_230 f) from (by
          unfold
            nb095_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0223
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_217
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_219 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_225
        D R S_cls E) ≠ (nb095_alpha_dummy_231 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0228
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_228 f) ≠ (nb095_alpha_dummy_232 f) from (by
          unfold
            nb095_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0229
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_225 D R S_cls E) ≠
        (nb095_alpha_dummy_229 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0226
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_228 f) ≠ (nb095_alpha_dummy_230 f) from (by
          unfold
            nb095_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0227
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_225 D R S_cls E), (nb095_alpha_dummy_228 f)),
        ((nb095_alpha_dummy_224 D R S_cls E), (nb095_alpha_dummy_227 f)),
        ((nb095_alpha_dummy_223 D R S_cls E), (nb095_alpha_dummy_226 f)),
        ((nb095_alpha_dummy_221 D R S_cls E), (nb095_alpha_dummy_222 f)),
        ((nb095_alpha_dummy_217 D R S_cls E), (nb095_alpha_dummy_219 f)),
        ((nb095_alpha_dummy_218 D R S_cls E), (nb095_alpha_dummy_220 f)),
        ((nb095_alpha_dummy_210 D R S_cls E), (nb095_alpha_dummy_212 f)),
        ((nb095_alpha_dummy_209 D R S_cls E), (nb095_alpha_dummy_211 f)),
        ((nb095_alpha_dummy_215 D R S_cls E), (nb095_alpha_dummy_216 f)),
        ((nb095_alpha_dummy_213 D R S_cls E), (nb095_alpha_dummy_214 f)),
        ((nb095_alpha_dummy_206 D R S_cls E), (nb095_alpha_dummy_208 f)),
        ((nb095_alpha_dummy_205 D R S_cls E), (nb095_alpha_dummy_207 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_217 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_219 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_217
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_219 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_224 D R S_cls E) ≠ (nb095_alpha_dummy_235
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0232
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_227 f) ≠ (nb095_alpha_dummy_236 f) from (by
          unfold
            nb095_alpha_dummy_236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0233
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_224 D R S_cls E) ≠
        (nb095_alpha_dummy_233 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0230
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_227 f) ≠ (nb095_alpha_dummy_234 f) from (by
          unfold
            nb095_alpha_dummy_234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0231
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_217
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_219 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_224
        D R S_cls E) ≠ (nb095_alpha_dummy_235 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0232
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_227 f) ≠ (nb095_alpha_dummy_236 f) from (by
          unfold
            nb095_alpha_dummy_236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0233
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_224 D R S_cls E) ≠
        (nb095_alpha_dummy_233 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0230
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_227 f) ≠ (nb095_alpha_dummy_234 f) from (by
          unfold
            nb095_alpha_dummy_234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0231
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_217
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_219 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_225 D R S_cls E) ≠ (nb095_alpha_dummy_237
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_237;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0236
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_228 f) ≠ (nb095_alpha_dummy_238 f) from (by
          unfold
            nb095_alpha_dummy_238;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0237
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_225 D R S_cls E) ≠
        (nb095_alpha_dummy_233 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0234
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_228 f) ≠ (nb095_alpha_dummy_234 f) from (by
          unfold
            nb095_alpha_dummy_234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0235
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_225
        D R S_cls E) ≠ (nb095_alpha_dummy_237 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_237;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0236
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_228 f) ≠ (nb095_alpha_dummy_238 f) from (by
          unfold
            nb095_alpha_dummy_238;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0237
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_225 D R S_cls E) ≠
        (nb095_alpha_dummy_233 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0234
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_228 f) ≠ (nb095_alpha_dummy_234 f) from (by
          unfold
            nb095_alpha_dummy_234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0235
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_217 D R S_cls E) ≠ (nb095_alpha_dummy_221 D R S_cls E) from (by
          unfold nb095_alpha_dummy_221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0218 D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_219 f) ≠ (nb095_alpha_dummy_222 f) from (by
          unfold nb095_alpha_dummy_222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_221 D R S_cls E), (nb095_alpha_dummy_222 f)),
        ((nb095_alpha_dummy_217 D R S_cls E), (nb095_alpha_dummy_219 f)),
        ((nb095_alpha_dummy_218 D R S_cls E), (nb095_alpha_dummy_220 f)),
        ((nb095_alpha_dummy_210 D R S_cls E), (nb095_alpha_dummy_212 f)),
        ((nb095_alpha_dummy_209 D R S_cls E), (nb095_alpha_dummy_211 f)),
        ((nb095_alpha_dummy_215 D R S_cls E), (nb095_alpha_dummy_216 f)),
        ((nb095_alpha_dummy_213 D R S_cls E), (nb095_alpha_dummy_214 f)),
        ((nb095_alpha_dummy_206 D R S_cls E), (nb095_alpha_dummy_208 f)),
        ((nb095_alpha_dummy_205 D R S_cls E), (nb095_alpha_dummy_207 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show
        (nb095_alpha_dummy_217 D R S_cls E) ≠ (nb095_alpha_dummy_221 D R S_cls E) from (by
          unfold nb095_alpha_dummy_221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0218 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_219 f) ≠ (nb095_alpha_dummy_222 f) from (by
          unfold nb095_alpha_dummy_222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_217 D R S_cls E) ≠ (nb095_alpha_dummy_221 D R S_cls E) from (by
          unfold nb095_alpha_dummy_221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0218 D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_219 f) ≠ (nb095_alpha_dummy_222 f) from (by
          unfold nb095_alpha_dummy_222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_221 D R S_cls E), (nb095_alpha_dummy_222 f)),
        ((nb095_alpha_dummy_217 D R S_cls E), (nb095_alpha_dummy_219 f)),
        ((nb095_alpha_dummy_218 D R S_cls E), (nb095_alpha_dummy_220 f)),
        ((nb095_alpha_dummy_210 D R S_cls E), (nb095_alpha_dummy_212 f)),
        ((nb095_alpha_dummy_209 D R S_cls E), (nb095_alpha_dummy_211 f)),
        ((nb095_alpha_dummy_215 D R S_cls E), (nb095_alpha_dummy_216 f)),
        ((nb095_alpha_dummy_213 D R S_cls E), (nb095_alpha_dummy_214 f)),
        ((nb095_alpha_dummy_206 D R S_cls E), (nb095_alpha_dummy_208 f)),
        ((nb095_alpha_dummy_205 D R S_cls E), (nb095_alpha_dummy_207 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_cnnc)
        (by simp only [fv_syn_cnnc])))))))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb095_split_alpha_0021 x u D R S_cls f E)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex
                    (TAlphaWff.neg (nb095_split_alpha_0021 x u D R S_cls f E)))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
