/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C091M3BPart007

/-! NF weak partition development: NAR4H5C091M3BPart008. -/


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
noncomputable def nb091_split_alpha_0013 (D : Class) (R : Class) (p : Var) :
    TAlphaWff
      [((nb091_alpha_dummy_184 D R), (nb091_alpha_dummy_186 D R p)),
        ((nb091_alpha_dummy_183 D R), (nb091_alpha_dummy_185 D R p)),
        ((nb091_alpha_dummy_213 D R), (nb091_alpha_dummy_214 D R p)),
        ((nb091_alpha_dummy_187 D R), (nb091_alpha_dummy_188 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p),
        ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))]
      (Wff.imp (Wff.classMem (Class.cv (nb091_alpha_dummy_184 D R))
          (Class.cv (nb091_alpha_dummy_041 D R))) (Wff.neg
          (Wff.classEq (Class.cv (nb091_alpha_dummy_183 D R))
            (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_184 D R))) (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb091_alpha_dummy_186 D R p))
          (Class.cv (nb091_alpha_dummy_043 D R p))) (Wff.neg
          (Wff.classEq (Class.cv (nb091_alpha_dummy_185 D R p))
            (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_186 D R p)))
              (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_041 D R) ≠ (nb091_alpha_dummy_184 D R) from
            (by
              unfold nb091_alpha_dummy_184;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0210 D R) 1))))
          (show (nb091_alpha_dummy_043 D R p) ≠ (nb091_alpha_dummy_186 D R p) from (by
              unfold nb091_alpha_dummy_186;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0212 D R p) 1))))
          (TAlphaVar.there (show (nb091_alpha_dummy_041 D R) ≠ (nb091_alpha_dummy_183 D R) from
              (by
                unfold nb091_alpha_dummy_183;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0210 D R) 0))))
            (show (nb091_alpha_dummy_043 D R p) ≠ (nb091_alpha_dummy_185 D R p) from (by
                unfold nb091_alpha_dummy_185;
                with_reducible
                  exact
                    (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0212 D R p) 0))))
            (TAlphaVar.there
              (show (nb091_alpha_dummy_041 D R) ≠ (nb091_alpha_dummy_213 D R) from (by
                  unfold nb091_alpha_dummy_213;
                  with_reducible
                    exact
                      (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0214 D R) 0))))
              (show (nb091_alpha_dummy_043 D R p) ≠ (nb091_alpha_dummy_214 D R p) from (by
                  unfold nb091_alpha_dummy_214;
                  with_reducible
                    exact
                      (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0215 D R p) 0))))
              (TAlphaVar.there
                (show (nb091_alpha_dummy_041 D R) ≠ (nb091_alpha_dummy_187 D R) from (by
                    unfold nb091_alpha_dummy_187;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0211 D R) 0))))
                (show (nb091_alpha_dummy_043 D R p) ≠ (nb091_alpha_dummy_188 D R p) from (by
                    unfold nb091_alpha_dummy_188;
                    with_reducible
                      exact
                        (Nat.ne_of_lt
                          (mem_lt_freshVar (nb091_support_mem_0213 D R p) 0)))) (TAlphaVar.there
                  (freshVar_injective (((syn_chwniso D)).fv ∪ ((syn_csn (syn_chnwcutcode R D
                            (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))).fv)
                    (by decide)) (freshVar_injective (((syn_chwniso D)).fv ∪ ((syn_csn
                          (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p)))))).fv)
                    (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb091_alpha_dummy_042 D R))).fv ∪
                ((Class.cv (nb091_alpha_dummy_041 D R))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb091_alpha_dummy_044 D R p))).fv ∪
                ((Class.cv (nb091_alpha_dummy_043 D R p))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb091_alpha_dummy_184 D R) ≠ (nb091_alpha_dummy_191 D R)
                                      from (by
                                        unfold nb091_alpha_dummy_191;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0188 D R) 0)))) (show
                                      (nb091_alpha_dummy_186 D R p) ≠
                                        (nb091_alpha_dummy_193 D R p) from (by
                                        unfold nb091_alpha_dummy_193;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0189 D R p) 0))))
                                    (TAlphaVar.there (show (nb091_alpha_dummy_184 D R) ≠
        (nb091_alpha_dummy_192 D R) from (by
                                          unfold nb091_alpha_dummy_192;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0188 D R) 1)))) (show
                                        (nb091_alpha_dummy_186 D R p) ≠
        (nb091_alpha_dummy_194 D R p) from (by
                                          unfold nb091_alpha_dummy_194;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0189 D R p) 1))))
                                      (TAlphaVar.there (show (nb091_alpha_dummy_184 D R) ≠
        (nb091_alpha_dummy_217 D R) from (by
          unfold nb091_alpha_dummy_217;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0218 D R) 0)))) (show (nb091_alpha_dummy_186 D R p) ≠
        (nb091_alpha_dummy_218 D R p) from (by
          unfold nb091_alpha_dummy_218;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0219 D R p) 0)))) (TAlphaVar.there (show
        (nb091_alpha_dummy_184 D R) ≠ (nb091_alpha_dummy_215 D R) from (by
          unfold nb091_alpha_dummy_215;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0216 D R) 0)))) (show (nb091_alpha_dummy_186 D R p) ≠
        (nb091_alpha_dummy_216 D R p) from (by
          unfold nb091_alpha_dummy_216;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0217 D R p) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb091_alpha_dummy_184 D R))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb091_alpha_dummy_186 D R p))).fv)
                                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_191 D R) ≠ (nb091_alpha_dummy_198 D R) from
        (by
          unfold nb091_alpha_dummy_198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0192
                    D R)
                  1)))) (show (nb091_alpha_dummy_193 D R p) ≠ (nb091_alpha_dummy_201 D R p) from
        (by
          unfold nb091_alpha_dummy_201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0193
                    D R p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_191 D R) ≠
        (nb091_alpha_dummy_197 D R) from (by
          unfold nb091_alpha_dummy_197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0192
                    D R)
                  0)))) (show (nb091_alpha_dummy_193 D R p) ≠ (nb091_alpha_dummy_200 D R p) from
        (by
          unfold nb091_alpha_dummy_200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0193
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_191 D R) ≠
        (nb091_alpha_dummy_195 D R) from (by
          unfold
            nb091_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0190
                    D R)
                  0)))) (show (nb091_alpha_dummy_193 D R p) ≠ (nb091_alpha_dummy_196 D R p) from
        (by
          unfold
            nb091_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0191
                    D R p)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_199 D R), (nb091_alpha_dummy_202 D R p)),
        ((nb091_alpha_dummy_198 D R), (nb091_alpha_dummy_201 D R p)),
        ((nb091_alpha_dummy_197 D R), (nb091_alpha_dummy_200 D R p)),
        ((nb091_alpha_dummy_195 D R), (nb091_alpha_dummy_196 D R p)),
        ((nb091_alpha_dummy_191 D R), (nb091_alpha_dummy_193 D R p)),
        ((nb091_alpha_dummy_192 D R), (nb091_alpha_dummy_194 D R p)),
        ((nb091_alpha_dummy_217 D R), (nb091_alpha_dummy_218 D R p)),
        ((nb091_alpha_dummy_215 D R), (nb091_alpha_dummy_216 D R p)),
        ((nb091_alpha_dummy_184 D R), (nb091_alpha_dummy_186 D R p)),
        ((nb091_alpha_dummy_183 D R), (nb091_alpha_dummy_185 D R p)),
        ((nb091_alpha_dummy_213 D R), (nb091_alpha_dummy_214 D R p)),
        ((nb091_alpha_dummy_187 D R), (nb091_alpha_dummy_188 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_198 D R) ≠ (nb091_alpha_dummy_205 D R) from
        (by
          unfold
            nb091_alpha_dummy_205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0196
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_201 D R p) ≠ (nb091_alpha_dummy_206 D R p) from
        (by
          unfold
            nb091_alpha_dummy_206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0197
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_198 D R) ≠
        (nb091_alpha_dummy_203 D R) from (by
          unfold
            nb091_alpha_dummy_203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0194
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_201 D R p) ≠ (nb091_alpha_dummy_204 D R p) from
        (by
          unfold
            nb091_alpha_dummy_204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0195
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_191
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_193 D R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_199
        D R) ≠ (nb091_alpha_dummy_205 D R) from (by
          unfold
            nb091_alpha_dummy_205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0200
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_202 D R p) ≠ (nb091_alpha_dummy_206 D R p) from
        (by
          unfold
            nb091_alpha_dummy_206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0201
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_199 D R) ≠
        (nb091_alpha_dummy_203 D R) from (by
          unfold
            nb091_alpha_dummy_203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0198
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_202 D R p) ≠ (nb091_alpha_dummy_204 D R p) from
        (by
          unfold
            nb091_alpha_dummy_204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0199
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_198 D R) ≠ (nb091_alpha_dummy_205 D R) from
        (by
          unfold
            nb091_alpha_dummy_205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0196
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_201 D R p) ≠ (nb091_alpha_dummy_206 D R p) from
        (by
          unfold
            nb091_alpha_dummy_206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0197
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_198 D R) ≠
        (nb091_alpha_dummy_203 D R) from (by
          unfold
            nb091_alpha_dummy_203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0194
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_201 D R p) ≠ (nb091_alpha_dummy_204 D R p) from
        (by
          unfold
            nb091_alpha_dummy_204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0195
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_191
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_193 D R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_199
        D R) ≠ (nb091_alpha_dummy_205 D R) from (by
          unfold
            nb091_alpha_dummy_205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0200
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_202 D R p) ≠ (nb091_alpha_dummy_206 D R p) from
        (by
          unfold
            nb091_alpha_dummy_206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0201
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_199 D R) ≠
        (nb091_alpha_dummy_203 D R) from (by
          unfold
            nb091_alpha_dummy_203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0198
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_202 D R p) ≠ (nb091_alpha_dummy_204 D R p) from
        (by
          unfold
            nb091_alpha_dummy_204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0199
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_199 D R), (nb091_alpha_dummy_202 D R p)),
        ((nb091_alpha_dummy_198 D R), (nb091_alpha_dummy_201 D R p)),
        ((nb091_alpha_dummy_197 D R), (nb091_alpha_dummy_200 D R p)),
        ((nb091_alpha_dummy_195 D R), (nb091_alpha_dummy_196 D R p)),
        ((nb091_alpha_dummy_191 D R), (nb091_alpha_dummy_193 D R p)),
        ((nb091_alpha_dummy_192 D R), (nb091_alpha_dummy_194 D R p)),
        ((nb091_alpha_dummy_217 D R), (nb091_alpha_dummy_218 D R p)),
        ((nb091_alpha_dummy_215 D R), (nb091_alpha_dummy_216 D R p)),
        ((nb091_alpha_dummy_184 D R), (nb091_alpha_dummy_186 D R p)),
        ((nb091_alpha_dummy_183 D R), (nb091_alpha_dummy_185 D R p)),
        ((nb091_alpha_dummy_213 D R), (nb091_alpha_dummy_214 D R p)),
        ((nb091_alpha_dummy_187 D R), (nb091_alpha_dummy_188 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_191
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_193 D R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb091_alpha_dummy_191 D R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_193 D R p))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_198
        D R) ≠ (nb091_alpha_dummy_209 D R) from (by
          unfold
            nb091_alpha_dummy_209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0204
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_201 D R p) ≠ (nb091_alpha_dummy_210 D R p) from
        (by
          unfold
            nb091_alpha_dummy_210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0205
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_198 D R) ≠
        (nb091_alpha_dummy_207 D R) from (by
          unfold
            nb091_alpha_dummy_207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0202
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_201 D R p) ≠ (nb091_alpha_dummy_208 D R p) from
        (by
          unfold
            nb091_alpha_dummy_208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0203
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_191
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_193 D R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_198
        D R) ≠ (nb091_alpha_dummy_209 D R) from (by
          unfold
            nb091_alpha_dummy_209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0204
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_201 D R p) ≠ (nb091_alpha_dummy_210 D R p) from
        (by
          unfold
            nb091_alpha_dummy_210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0205
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_198 D R) ≠
        (nb091_alpha_dummy_207 D R) from (by
          unfold
            nb091_alpha_dummy_207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0202
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_201 D R p) ≠ (nb091_alpha_dummy_208 D R p) from
        (by
          unfold
            nb091_alpha_dummy_208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0203
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_191
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_193 D R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_199 D R) ≠ (nb091_alpha_dummy_211 D R) from
        (by
          unfold
            nb091_alpha_dummy_211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0208
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_202 D R p) ≠ (nb091_alpha_dummy_212 D R p) from
        (by
          unfold
            nb091_alpha_dummy_212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0209
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_199 D R) ≠
        (nb091_alpha_dummy_207 D R) from (by
          unfold
            nb091_alpha_dummy_207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0206
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_202 D R p) ≠ (nb091_alpha_dummy_208 D R p) from
        (by
          unfold
            nb091_alpha_dummy_208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0207
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_199
        D R) ≠ (nb091_alpha_dummy_211 D R) from (by
          unfold
            nb091_alpha_dummy_211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0208
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_202 D R p) ≠ (nb091_alpha_dummy_212 D R p) from
        (by
          unfold
            nb091_alpha_dummy_212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0209
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_199 D R) ≠
        (nb091_alpha_dummy_207 D R) from (by
          unfold
            nb091_alpha_dummy_207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0206
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_202 D R p) ≠ (nb091_alpha_dummy_208 D R p) from
        (by
          unfold
            nb091_alpha_dummy_208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0207
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_191 D R) ≠
        (nb091_alpha_dummy_195 D R) from (by
          unfold nb091_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0190 D R)
                  0)))) (show (nb091_alpha_dummy_193 D R p) ≠ (nb091_alpha_dummy_196 D R p) from
        (by
          unfold nb091_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0191 D R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_195 D R), (nb091_alpha_dummy_196 D R p)),
        ((nb091_alpha_dummy_191 D R), (nb091_alpha_dummy_193 D R p)),
        ((nb091_alpha_dummy_192 D R), (nb091_alpha_dummy_194 D R p)),
        ((nb091_alpha_dummy_217 D R), (nb091_alpha_dummy_218 D R p)),
        ((nb091_alpha_dummy_215 D R), (nb091_alpha_dummy_216 D R p)),
        ((nb091_alpha_dummy_184 D R), (nb091_alpha_dummy_186 D R p)),
        ((nb091_alpha_dummy_183 D R), (nb091_alpha_dummy_185 D R p)),
        ((nb091_alpha_dummy_213 D R), (nb091_alpha_dummy_214 D R p)),
        ((nb091_alpha_dummy_187 D R), (nb091_alpha_dummy_188 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_191 D R) ≠ (nb091_alpha_dummy_195 D R) from
        (by
          unfold nb091_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0190 D R) 0)))) (show (nb091_alpha_dummy_193 D R p) ≠
        (nb091_alpha_dummy_196 D R p) from (by
          unfold nb091_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0191 D R p)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_191 D R) ≠
        (nb091_alpha_dummy_195 D R) from (by
          unfold nb091_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0190 D R)
                  0)))) (show (nb091_alpha_dummy_193 D R p) ≠ (nb091_alpha_dummy_196 D R p) from
        (by
          unfold nb091_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0191 D R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_195 D R), (nb091_alpha_dummy_196 D R p)),
        ((nb091_alpha_dummy_191 D R), (nb091_alpha_dummy_193 D R p)),
        ((nb091_alpha_dummy_192 D R), (nb091_alpha_dummy_194 D R p)),
        ((nb091_alpha_dummy_217 D R), (nb091_alpha_dummy_218 D R p)),
        ((nb091_alpha_dummy_215 D R), (nb091_alpha_dummy_216 D R p)),
        ((nb091_alpha_dummy_184 D R), (nb091_alpha_dummy_186 D R p)),
        ((nb091_alpha_dummy_183 D R), (nb091_alpha_dummy_185 D R p)),
        ((nb091_alpha_dummy_213 D R), (nb091_alpha_dummy_214 D R p)),
        ((nb091_alpha_dummy_187 D R), (nb091_alpha_dummy_188 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb091_alpha_dummy_184 D R) ≠ (nb091_alpha_dummy_191 D R)
                                      from (by
                                        unfold nb091_alpha_dummy_191;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0188 D R) 0)))) (show
                                      (nb091_alpha_dummy_186 D R p) ≠
                                        (nb091_alpha_dummy_193 D R p) from (by
                                        unfold nb091_alpha_dummy_193;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0189 D R p) 0))))
                                    (TAlphaVar.there (show (nb091_alpha_dummy_184 D R) ≠
        (nb091_alpha_dummy_192 D R) from (by
                                          unfold nb091_alpha_dummy_192;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0188 D R) 1)))) (show
                                        (nb091_alpha_dummy_186 D R p) ≠
        (nb091_alpha_dummy_194 D R p) from (by
                                          unfold nb091_alpha_dummy_194;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0189 D R p) 1))))
                                      (TAlphaVar.there (show (nb091_alpha_dummy_184 D R) ≠
        (nb091_alpha_dummy_217 D R) from (by
          unfold nb091_alpha_dummy_217;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0218 D R) 0)))) (show (nb091_alpha_dummy_186 D R p) ≠
        (nb091_alpha_dummy_218 D R p) from (by
          unfold nb091_alpha_dummy_218;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0219 D R p) 0)))) (TAlphaVar.there (show
        (nb091_alpha_dummy_184 D R) ≠ (nb091_alpha_dummy_215 D R) from (by
          unfold nb091_alpha_dummy_215;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0216 D R) 0)))) (show (nb091_alpha_dummy_186 D R p) ≠
        (nb091_alpha_dummy_216 D R p) from (by
          unfold nb091_alpha_dummy_216;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0217 D R p) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb091_alpha_dummy_184 D R))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb091_alpha_dummy_186 D R p))).fv)
                                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_191 D R) ≠ (nb091_alpha_dummy_198 D R) from
        (by
          unfold nb091_alpha_dummy_198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0192
                    D R)
                  1)))) (show (nb091_alpha_dummy_193 D R p) ≠ (nb091_alpha_dummy_201 D R p) from
        (by
          unfold nb091_alpha_dummy_201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0193
                    D R p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_191 D R) ≠
        (nb091_alpha_dummy_197 D R) from (by
          unfold nb091_alpha_dummy_197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0192
                    D R)
                  0)))) (show (nb091_alpha_dummy_193 D R p) ≠ (nb091_alpha_dummy_200 D R p) from
        (by
          unfold nb091_alpha_dummy_200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0193
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_191 D R) ≠
        (nb091_alpha_dummy_195 D R) from (by
          unfold
            nb091_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0190
                    D R)
                  0)))) (show (nb091_alpha_dummy_193 D R p) ≠ (nb091_alpha_dummy_196 D R p) from
        (by
          unfold
            nb091_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0191
                    D R p)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_199 D R), (nb091_alpha_dummy_202 D R p)),
        ((nb091_alpha_dummy_198 D R), (nb091_alpha_dummy_201 D R p)),
        ((nb091_alpha_dummy_197 D R), (nb091_alpha_dummy_200 D R p)),
        ((nb091_alpha_dummy_195 D R), (nb091_alpha_dummy_196 D R p)),
        ((nb091_alpha_dummy_191 D R), (nb091_alpha_dummy_193 D R p)),
        ((nb091_alpha_dummy_192 D R), (nb091_alpha_dummy_194 D R p)),
        ((nb091_alpha_dummy_217 D R), (nb091_alpha_dummy_218 D R p)),
        ((nb091_alpha_dummy_215 D R), (nb091_alpha_dummy_216 D R p)),
        ((nb091_alpha_dummy_184 D R), (nb091_alpha_dummy_186 D R p)),
        ((nb091_alpha_dummy_183 D R), (nb091_alpha_dummy_185 D R p)),
        ((nb091_alpha_dummy_213 D R), (nb091_alpha_dummy_214 D R p)),
        ((nb091_alpha_dummy_187 D R), (nb091_alpha_dummy_188 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_198 D R) ≠ (nb091_alpha_dummy_205 D R) from
        (by
          unfold
            nb091_alpha_dummy_205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0196
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_201 D R p) ≠ (nb091_alpha_dummy_206 D R p) from
        (by
          unfold
            nb091_alpha_dummy_206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0197
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_198 D R) ≠
        (nb091_alpha_dummy_203 D R) from (by
          unfold
            nb091_alpha_dummy_203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0194
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_201 D R p) ≠ (nb091_alpha_dummy_204 D R p) from
        (by
          unfold
            nb091_alpha_dummy_204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0195
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_191
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_193 D R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_199
        D R) ≠ (nb091_alpha_dummy_205 D R) from (by
          unfold
            nb091_alpha_dummy_205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0200
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_202 D R p) ≠ (nb091_alpha_dummy_206 D R p) from
        (by
          unfold
            nb091_alpha_dummy_206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0201
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_199 D R) ≠
        (nb091_alpha_dummy_203 D R) from (by
          unfold
            nb091_alpha_dummy_203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0198
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_202 D R p) ≠ (nb091_alpha_dummy_204 D R p) from
        (by
          unfold
            nb091_alpha_dummy_204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0199
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_198 D R) ≠ (nb091_alpha_dummy_205 D R) from
        (by
          unfold
            nb091_alpha_dummy_205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0196
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_201 D R p) ≠ (nb091_alpha_dummy_206 D R p) from
        (by
          unfold
            nb091_alpha_dummy_206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0197
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_198 D R) ≠
        (nb091_alpha_dummy_203 D R) from (by
          unfold
            nb091_alpha_dummy_203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0194
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_201 D R p) ≠ (nb091_alpha_dummy_204 D R p) from
        (by
          unfold
            nb091_alpha_dummy_204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0195
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_191
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_193 D R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_199
        D R) ≠ (nb091_alpha_dummy_205 D R) from (by
          unfold
            nb091_alpha_dummy_205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0200
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_202 D R p) ≠ (nb091_alpha_dummy_206 D R p) from
        (by
          unfold
            nb091_alpha_dummy_206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0201
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_199 D R) ≠
        (nb091_alpha_dummy_203 D R) from (by
          unfold
            nb091_alpha_dummy_203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0198
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_202 D R p) ≠ (nb091_alpha_dummy_204 D R p) from
        (by
          unfold
            nb091_alpha_dummy_204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0199
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_199 D R), (nb091_alpha_dummy_202 D R p)),
        ((nb091_alpha_dummy_198 D R), (nb091_alpha_dummy_201 D R p)),
        ((nb091_alpha_dummy_197 D R), (nb091_alpha_dummy_200 D R p)),
        ((nb091_alpha_dummy_195 D R), (nb091_alpha_dummy_196 D R p)),
        ((nb091_alpha_dummy_191 D R), (nb091_alpha_dummy_193 D R p)),
        ((nb091_alpha_dummy_192 D R), (nb091_alpha_dummy_194 D R p)),
        ((nb091_alpha_dummy_217 D R), (nb091_alpha_dummy_218 D R p)),
        ((nb091_alpha_dummy_215 D R), (nb091_alpha_dummy_216 D R p)),
        ((nb091_alpha_dummy_184 D R), (nb091_alpha_dummy_186 D R p)),
        ((nb091_alpha_dummy_183 D R), (nb091_alpha_dummy_185 D R p)),
        ((nb091_alpha_dummy_213 D R), (nb091_alpha_dummy_214 D R p)),
        ((nb091_alpha_dummy_187 D R), (nb091_alpha_dummy_188 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_191
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_193 D R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb091_alpha_dummy_191 D R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_193 D R p))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_198
        D R) ≠ (nb091_alpha_dummy_209 D R) from (by
          unfold
            nb091_alpha_dummy_209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0204
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_201 D R p) ≠ (nb091_alpha_dummy_210 D R p) from
        (by
          unfold
            nb091_alpha_dummy_210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0205
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_198 D R) ≠
        (nb091_alpha_dummy_207 D R) from (by
          unfold
            nb091_alpha_dummy_207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0202
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_201 D R p) ≠ (nb091_alpha_dummy_208 D R p) from
        (by
          unfold
            nb091_alpha_dummy_208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0203
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_191
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_193 D R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_198
        D R) ≠ (nb091_alpha_dummy_209 D R) from (by
          unfold
            nb091_alpha_dummy_209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0204
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_201 D R p) ≠ (nb091_alpha_dummy_210 D R p) from
        (by
          unfold
            nb091_alpha_dummy_210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0205
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_198 D R) ≠
        (nb091_alpha_dummy_207 D R) from (by
          unfold
            nb091_alpha_dummy_207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0202
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_201 D R p) ≠ (nb091_alpha_dummy_208 D R p) from
        (by
          unfold
            nb091_alpha_dummy_208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0203
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_191
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_193 D R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_199 D R) ≠ (nb091_alpha_dummy_211 D R) from
        (by
          unfold
            nb091_alpha_dummy_211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0208
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_202 D R p) ≠ (nb091_alpha_dummy_212 D R p) from
        (by
          unfold
            nb091_alpha_dummy_212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0209
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_199 D R) ≠
        (nb091_alpha_dummy_207 D R) from (by
          unfold
            nb091_alpha_dummy_207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0206
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_202 D R p) ≠ (nb091_alpha_dummy_208 D R p) from
        (by
          unfold
            nb091_alpha_dummy_208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0207
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_199
        D R) ≠ (nb091_alpha_dummy_211 D R) from (by
          unfold
            nb091_alpha_dummy_211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0208
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_202 D R p) ≠ (nb091_alpha_dummy_212 D R p) from
        (by
          unfold
            nb091_alpha_dummy_212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0209
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_199 D R) ≠
        (nb091_alpha_dummy_207 D R) from (by
          unfold
            nb091_alpha_dummy_207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0206
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_202 D R p) ≠ (nb091_alpha_dummy_208 D R p) from
        (by
          unfold
            nb091_alpha_dummy_208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0207
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_191 D R) ≠
        (nb091_alpha_dummy_195 D R) from (by
          unfold nb091_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0190 D R)
                  0)))) (show (nb091_alpha_dummy_193 D R p) ≠ (nb091_alpha_dummy_196 D R p) from
        (by
          unfold nb091_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0191 D R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_195 D R), (nb091_alpha_dummy_196 D R p)),
        ((nb091_alpha_dummy_191 D R), (nb091_alpha_dummy_193 D R p)),
        ((nb091_alpha_dummy_192 D R), (nb091_alpha_dummy_194 D R p)),
        ((nb091_alpha_dummy_217 D R), (nb091_alpha_dummy_218 D R p)),
        ((nb091_alpha_dummy_215 D R), (nb091_alpha_dummy_216 D R p)),
        ((nb091_alpha_dummy_184 D R), (nb091_alpha_dummy_186 D R p)),
        ((nb091_alpha_dummy_183 D R), (nb091_alpha_dummy_185 D R p)),
        ((nb091_alpha_dummy_213 D R), (nb091_alpha_dummy_214 D R p)),
        ((nb091_alpha_dummy_187 D R), (nb091_alpha_dummy_188 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_191 D R) ≠ (nb091_alpha_dummy_195 D R) from
        (by
          unfold nb091_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0190 D R) 0)))) (show (nb091_alpha_dummy_193 D R p) ≠
        (nb091_alpha_dummy_196 D R p) from (by
          unfold nb091_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0191 D R p)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_191 D R) ≠
        (nb091_alpha_dummy_195 D R) from (by
          unfold nb091_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0190 D R)
                  0)))) (show (nb091_alpha_dummy_193 D R p) ≠ (nb091_alpha_dummy_196 D R p) from
        (by
          unfold nb091_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0191 D R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_195 D R), (nb091_alpha_dummy_196 D R p)),
        ((nb091_alpha_dummy_191 D R), (nb091_alpha_dummy_193 D R p)),
        ((nb091_alpha_dummy_192 D R), (nb091_alpha_dummy_194 D R p)),
        ((nb091_alpha_dummy_217 D R), (nb091_alpha_dummy_218 D R p)),
        ((nb091_alpha_dummy_215 D R), (nb091_alpha_dummy_216 D R p)),
        ((nb091_alpha_dummy_184 D R), (nb091_alpha_dummy_186 D R p)),
        ((nb091_alpha_dummy_183 D R), (nb091_alpha_dummy_185 D R p)),
        ((nb091_alpha_dummy_213 D R), (nb091_alpha_dummy_214 D R p)),
        ((nb091_alpha_dummy_187 D R), (nb091_alpha_dummy_188 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb091_alpha_dummy_215 D R), (nb091_alpha_dummy_216 D R p)),
                    ((nb091_alpha_dummy_184 D R), (nb091_alpha_dummy_186 D R p)),
                    ((nb091_alpha_dummy_183 D R), (nb091_alpha_dummy_185 D R p)),
                    ((nb091_alpha_dummy_213 D R), (nb091_alpha_dummy_214 D R p)),
                    ((nb091_alpha_dummy_187 D R), (nb091_alpha_dummy_188 D R p)),
                    ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
                    ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
                    ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
                    ((nb091_alpha_dummy_000 D R), p),
                    ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))]
                  (syn_ccompl (syn_csn (syn_c0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

@[expose]
noncomputable def nb091_split_alpha_0014 (D : Class) (R : Class) (p : Var) :
    TAlphaWff
      [((nb091_alpha_dummy_187 D R), (nb091_alpha_dummy_188 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p),
        ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))]
      (Wff.imp (Wff.classMem (Class.cv (nb091_alpha_dummy_187 D R)) (syn_ccompl
            (Class.cab (nb091_alpha_dummy_183 D R)
              (syn_wrex (nb091_alpha_dummy_184 D R) (Class.cv (nb091_alpha_dummy_042 D R))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_183 D R))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_184 D R)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb091_alpha_dummy_187 D R)) (syn_ccompl
              (Class.cab (nb091_alpha_dummy_183 D R) (syn_wrex (nb091_alpha_dummy_184 D R)
                  (Class.cv (nb091_alpha_dummy_041 D R))
                  (Wff.classEq (Class.cv (nb091_alpha_dummy_183 D R))
                    (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_184 D R)))
                      (syn_csn (syn_c0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb091_alpha_dummy_188 D R p)) (syn_ccompl
            (Class.cab (nb091_alpha_dummy_185 D R p) (syn_wrex (nb091_alpha_dummy_186 D R p)
                (Class.cv (nb091_alpha_dummy_044 D R p))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_185 D R p))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_186 D R p)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb091_alpha_dummy_188 D R p)) (syn_ccompl
              (Class.cab (nb091_alpha_dummy_185 D R p) (syn_wrex (nb091_alpha_dummy_186 D R p)
                  (Class.cv (nb091_alpha_dummy_043 D R p))
                  (Wff.classEq (Class.cv (nb091_alpha_dummy_185 D R p))
                    (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_186 D R p)))
                      (syn_csn (syn_c0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb091_alpha_dummy_042 D R) ≠ (nb091_alpha_dummy_184 D R) from
                            (by
                              unfold nb091_alpha_dummy_184;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb091_support_mem_0182 D R) 1)))) (show
                            (nb091_alpha_dummy_044 D R p) ≠ (nb091_alpha_dummy_186 D R p) from
                            (by
                              unfold nb091_alpha_dummy_186;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb091_support_mem_0184 D R p) 1))))
                          (TAlphaVar.there (show
                              (nb091_alpha_dummy_042 D R) ≠ (nb091_alpha_dummy_183 D R) from (by
                                unfold nb091_alpha_dummy_183;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0182 D R) 0)))) (show
                              (nb091_alpha_dummy_044 D R p) ≠ (nb091_alpha_dummy_185 D R p) from
                              (by
                                unfold nb091_alpha_dummy_185;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0184 D R p)
                                        0)))) (TAlphaVar.there (show
                                (nb091_alpha_dummy_042 D R) ≠ (nb091_alpha_dummy_189 D R) from
                                (by
                                  unfold nb091_alpha_dummy_189;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb091_support_mem_0186 D R)
                                          0)))) (show (nb091_alpha_dummy_044 D R p) ≠
                                  (nb091_alpha_dummy_190 D R p) from (by
                                  unfold nb091_alpha_dummy_190;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb091_support_mem_0187 D R p)
                                          0)))) (TAlphaVar.there (show
                                  (nb091_alpha_dummy_042 D R) ≠ (nb091_alpha_dummy_187 D R) from
                                  (by
                                    unfold nb091_alpha_dummy_187;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb091_support_mem_0183 D R)
                                            0)))) (show (nb091_alpha_dummy_044 D R p) ≠
                                    (nb091_alpha_dummy_188 D R p) from (by
                                    unfold nb091_alpha_dummy_188;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb091_support_mem_0185 D R p)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb091_alpha_dummy_042 D R))).fv ∪
                              ((Class.cv (nb091_alpha_dummy_041 D R))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb091_alpha_dummy_044 D R p))).fv ∪
                              ((Class.cv (nb091_alpha_dummy_043 D R p))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb091_alpha_dummy_184 D R) ≠ (nb091_alpha_dummy_191 D R)
                                    from (by
                                      unfold nb091_alpha_dummy_191;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb091_support_mem_0188 D R)
                                              0)))) (show (nb091_alpha_dummy_186 D R p) ≠
                                      (nb091_alpha_dummy_193 D R p) from (by
                                      unfold nb091_alpha_dummy_193;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb091_support_mem_0189 D R p) 0))))
                                  (TAlphaVar.there (show (nb091_alpha_dummy_184 D R) ≠
                                        (nb091_alpha_dummy_192 D R) from (by
                                        unfold nb091_alpha_dummy_192;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0188 D R) 1)))) (show
                                      (nb091_alpha_dummy_186 D R p) ≠
                                        (nb091_alpha_dummy_194 D R p) from (by
                                        unfold nb091_alpha_dummy_194;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0189 D R p) 1))))
                                    (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                    (((Class.cv (nb091_alpha_dummy_184 D R))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb091_alpha_dummy_186 D R p))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb091_alpha_dummy_191 D R) ≠ (nb091_alpha_dummy_198 D R) from (by
          unfold nb091_alpha_dummy_198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0192 D
                    R)
                  1)))) (show (nb091_alpha_dummy_193 D R p) ≠ (nb091_alpha_dummy_201 D R p) from
        (by
          unfold nb091_alpha_dummy_201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0193 D
                    R p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_191 D R) ≠
        (nb091_alpha_dummy_197 D R) from (by
          unfold nb091_alpha_dummy_197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0192
                    D R)
                  0)))) (show (nb091_alpha_dummy_193 D R p) ≠ (nb091_alpha_dummy_200 D R p) from
        (by
          unfold nb091_alpha_dummy_200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0193
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_191 D R) ≠
        (nb091_alpha_dummy_195 D R) from (by
          unfold nb091_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0190
                    D R)
                  0)))) (show (nb091_alpha_dummy_193 D R p) ≠ (nb091_alpha_dummy_196 D R p) from
        (by
          unfold nb091_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0191
                    D R p)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_199 D R), (nb091_alpha_dummy_202 D R p)),
        ((nb091_alpha_dummy_198 D R), (nb091_alpha_dummy_201 D R p)),
        ((nb091_alpha_dummy_197 D R), (nb091_alpha_dummy_200 D R p)),
        ((nb091_alpha_dummy_195 D R), (nb091_alpha_dummy_196 D R p)),
        ((nb091_alpha_dummy_191 D R), (nb091_alpha_dummy_193 D R p)),
        ((nb091_alpha_dummy_192 D R), (nb091_alpha_dummy_194 D R p)),
        ((nb091_alpha_dummy_184 D R), (nb091_alpha_dummy_186 D R p)),
        ((nb091_alpha_dummy_183 D R), (nb091_alpha_dummy_185 D R p)),
        ((nb091_alpha_dummy_189 D R), (nb091_alpha_dummy_190 D R p)),
        ((nb091_alpha_dummy_187 D R), (nb091_alpha_dummy_188 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_198 D R) ≠ (nb091_alpha_dummy_205 D R) from
        (by
          unfold
            nb091_alpha_dummy_205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0196
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_201 D R p) ≠ (nb091_alpha_dummy_206 D R p) from
        (by
          unfold
            nb091_alpha_dummy_206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0197
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_198 D R) ≠
        (nb091_alpha_dummy_203 D R) from (by
          unfold
            nb091_alpha_dummy_203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0194
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_201 D R p) ≠ (nb091_alpha_dummy_204 D R p) from
        (by
          unfold
            nb091_alpha_dummy_204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0195
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_191
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_193 D R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_199
        D R) ≠ (nb091_alpha_dummy_205 D R) from (by
          unfold
            nb091_alpha_dummy_205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0200
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_202 D R p) ≠ (nb091_alpha_dummy_206 D R p) from
        (by
          unfold
            nb091_alpha_dummy_206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0201
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_199 D R) ≠
        (nb091_alpha_dummy_203 D R) from (by
          unfold
            nb091_alpha_dummy_203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0198
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_202 D R p) ≠ (nb091_alpha_dummy_204 D R p) from
        (by
          unfold
            nb091_alpha_dummy_204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0199
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_198 D R) ≠ (nb091_alpha_dummy_205 D R) from
        (by
          unfold
            nb091_alpha_dummy_205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0196
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_201 D R p) ≠ (nb091_alpha_dummy_206 D R p) from
        (by
          unfold
            nb091_alpha_dummy_206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0197
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_198 D R) ≠
        (nb091_alpha_dummy_203 D R) from (by
          unfold
            nb091_alpha_dummy_203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0194
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_201 D R p) ≠ (nb091_alpha_dummy_204 D R p) from
        (by
          unfold
            nb091_alpha_dummy_204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0195
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_191
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_193 D R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_199
        D R) ≠ (nb091_alpha_dummy_205 D R) from (by
          unfold
            nb091_alpha_dummy_205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0200
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_202 D R p) ≠ (nb091_alpha_dummy_206 D R p) from
        (by
          unfold
            nb091_alpha_dummy_206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0201
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_199 D R) ≠
        (nb091_alpha_dummy_203 D R) from (by
          unfold
            nb091_alpha_dummy_203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0198
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_202 D R p) ≠ (nb091_alpha_dummy_204 D R p) from
        (by
          unfold
            nb091_alpha_dummy_204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0199
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_199 D R), (nb091_alpha_dummy_202 D R p)),
        ((nb091_alpha_dummy_198 D R), (nb091_alpha_dummy_201 D R p)),
        ((nb091_alpha_dummy_197 D R), (nb091_alpha_dummy_200 D R p)),
        ((nb091_alpha_dummy_195 D R), (nb091_alpha_dummy_196 D R p)),
        ((nb091_alpha_dummy_191 D R), (nb091_alpha_dummy_193 D R p)),
        ((nb091_alpha_dummy_192 D R), (nb091_alpha_dummy_194 D R p)),
        ((nb091_alpha_dummy_184 D R), (nb091_alpha_dummy_186 D R p)),
        ((nb091_alpha_dummy_183 D R), (nb091_alpha_dummy_185 D R p)),
        ((nb091_alpha_dummy_189 D R), (nb091_alpha_dummy_190 D R p)),
        ((nb091_alpha_dummy_187 D R), (nb091_alpha_dummy_188 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_191 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_193 D R p))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_191 D R))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_193
        D R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_198 D R) ≠ (nb091_alpha_dummy_209 D R) from
        (by
          unfold
            nb091_alpha_dummy_209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0204
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_201 D R p) ≠ (nb091_alpha_dummy_210 D R p) from
        (by
          unfold
            nb091_alpha_dummy_210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0205
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_198 D R) ≠
        (nb091_alpha_dummy_207 D R) from (by
          unfold
            nb091_alpha_dummy_207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0202
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_201 D R p) ≠ (nb091_alpha_dummy_208 D R p) from
        (by
          unfold
            nb091_alpha_dummy_208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0203
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_191
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_193 D R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_198
        D R) ≠ (nb091_alpha_dummy_209 D R) from (by
          unfold
            nb091_alpha_dummy_209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0204
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_201 D R p) ≠ (nb091_alpha_dummy_210 D R p) from
        (by
          unfold
            nb091_alpha_dummy_210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0205
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_198 D R) ≠
        (nb091_alpha_dummy_207 D R) from (by
          unfold
            nb091_alpha_dummy_207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0202
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_201 D R p) ≠ (nb091_alpha_dummy_208 D R p) from
        (by
          unfold
            nb091_alpha_dummy_208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0203
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_191
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_193 D R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_199 D R) ≠ (nb091_alpha_dummy_211 D R) from
        (by
          unfold
            nb091_alpha_dummy_211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0208
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_202 D R p) ≠ (nb091_alpha_dummy_212 D R p) from
        (by
          unfold
            nb091_alpha_dummy_212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0209
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_199 D R) ≠
        (nb091_alpha_dummy_207 D R) from (by
          unfold
            nb091_alpha_dummy_207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0206
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_202 D R p) ≠ (nb091_alpha_dummy_208 D R p) from
        (by
          unfold
            nb091_alpha_dummy_208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0207
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_199
        D R) ≠ (nb091_alpha_dummy_211 D R) from (by
          unfold
            nb091_alpha_dummy_211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0208
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_202 D R p) ≠ (nb091_alpha_dummy_212 D R p) from
        (by
          unfold
            nb091_alpha_dummy_212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0209
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_199 D R) ≠
        (nb091_alpha_dummy_207 D R) from (by
          unfold
            nb091_alpha_dummy_207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0206
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_202 D R p) ≠ (nb091_alpha_dummy_208 D R p) from
        (by
          unfold
            nb091_alpha_dummy_208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0207
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb091_alpha_dummy_191 D R) ≠ (nb091_alpha_dummy_195 D R) from (by
          unfold nb091_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0190 D R) 0)))) (show (nb091_alpha_dummy_193 D R p) ≠
        (nb091_alpha_dummy_196 D R p) from (by
          unfold nb091_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0191 D R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_195 D R), (nb091_alpha_dummy_196 D R p)),
        ((nb091_alpha_dummy_191 D R), (nb091_alpha_dummy_193 D R p)),
        ((nb091_alpha_dummy_192 D R), (nb091_alpha_dummy_194 D R p)),
        ((nb091_alpha_dummy_184 D R), (nb091_alpha_dummy_186 D R p)),
        ((nb091_alpha_dummy_183 D R), (nb091_alpha_dummy_185 D R p)),
        ((nb091_alpha_dummy_189 D R), (nb091_alpha_dummy_190 D R p)),
        ((nb091_alpha_dummy_187 D R), (nb091_alpha_dummy_188 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb091_alpha_dummy_191 D R) ≠
        (nb091_alpha_dummy_195 D R) from (by
          unfold nb091_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0190 D R) 0)))) (show (nb091_alpha_dummy_193 D R p) ≠
        (nb091_alpha_dummy_196 D R p) from (by
          unfold nb091_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0191 D R p) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb091_alpha_dummy_191 D R) ≠ (nb091_alpha_dummy_195 D R) from (by
          unfold nb091_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0190 D R) 0)))) (show (nb091_alpha_dummy_193 D R p) ≠
        (nb091_alpha_dummy_196 D R p) from (by
          unfold nb091_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0191 D R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_195 D R), (nb091_alpha_dummy_196 D R p)),
        ((nb091_alpha_dummy_191 D R), (nb091_alpha_dummy_193 D R p)),
        ((nb091_alpha_dummy_192 D R), (nb091_alpha_dummy_194 D R p)),
        ((nb091_alpha_dummy_184 D R), (nb091_alpha_dummy_186 D R p)),
        ((nb091_alpha_dummy_183 D R), (nb091_alpha_dummy_185 D R p)),
        ((nb091_alpha_dummy_189 D R), (nb091_alpha_dummy_190 D R p)),
        ((nb091_alpha_dummy_187 D R), (nb091_alpha_dummy_188 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb091_alpha_dummy_042 D R) ≠ (nb091_alpha_dummy_184 D R) from
                            (by
                              unfold nb091_alpha_dummy_184;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb091_support_mem_0182 D R) 1)))) (show
                            (nb091_alpha_dummy_044 D R p) ≠ (nb091_alpha_dummy_186 D R p) from
                            (by
                              unfold nb091_alpha_dummy_186;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb091_support_mem_0184 D R p) 1))))
                          (TAlphaVar.there (show
                              (nb091_alpha_dummy_042 D R) ≠ (nb091_alpha_dummy_183 D R) from (by
                                unfold nb091_alpha_dummy_183;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0182 D R) 0)))) (show
                              (nb091_alpha_dummy_044 D R p) ≠ (nb091_alpha_dummy_185 D R p) from
                              (by
                                unfold nb091_alpha_dummy_185;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0184 D R p)
                                        0)))) (TAlphaVar.there (show
                                (nb091_alpha_dummy_042 D R) ≠ (nb091_alpha_dummy_189 D R) from
                                (by
                                  unfold nb091_alpha_dummy_189;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb091_support_mem_0186 D R)
                                          0)))) (show (nb091_alpha_dummy_044 D R p) ≠
                                  (nb091_alpha_dummy_190 D R p) from (by
                                  unfold nb091_alpha_dummy_190;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb091_support_mem_0187 D R p)
                                          0)))) (TAlphaVar.there (show
                                  (nb091_alpha_dummy_042 D R) ≠ (nb091_alpha_dummy_187 D R) from
                                  (by
                                    unfold nb091_alpha_dummy_187;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb091_support_mem_0183 D R)
                                            0)))) (show (nb091_alpha_dummy_044 D R p) ≠
                                    (nb091_alpha_dummy_188 D R p) from (by
                                    unfold nb091_alpha_dummy_188;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb091_support_mem_0185 D R p)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb091_alpha_dummy_042 D R))).fv ∪
                              ((Class.cv (nb091_alpha_dummy_041 D R))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb091_alpha_dummy_044 D R p))).fv ∪
                              ((Class.cv (nb091_alpha_dummy_043 D R p))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb091_alpha_dummy_184 D R) ≠ (nb091_alpha_dummy_191 D R)
                                    from (by
                                      unfold nb091_alpha_dummy_191;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb091_support_mem_0188 D R)
                                              0)))) (show (nb091_alpha_dummy_186 D R p) ≠
                                      (nb091_alpha_dummy_193 D R p) from (by
                                      unfold nb091_alpha_dummy_193;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb091_support_mem_0189 D R p) 0))))
                                  (TAlphaVar.there (show (nb091_alpha_dummy_184 D R) ≠
                                        (nb091_alpha_dummy_192 D R) from (by
                                        unfold nb091_alpha_dummy_192;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0188 D R) 1)))) (show
                                      (nb091_alpha_dummy_186 D R p) ≠
                                        (nb091_alpha_dummy_194 D R p) from (by
                                        unfold nb091_alpha_dummy_194;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0189 D R p) 1))))
                                    (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                    (((Class.cv (nb091_alpha_dummy_184 D R))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb091_alpha_dummy_186 D R p))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb091_alpha_dummy_191 D R) ≠ (nb091_alpha_dummy_198 D R) from (by
          unfold nb091_alpha_dummy_198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0192 D
                    R)
                  1)))) (show (nb091_alpha_dummy_193 D R p) ≠ (nb091_alpha_dummy_201 D R p) from
        (by
          unfold nb091_alpha_dummy_201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0193 D
                    R p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_191 D R) ≠
        (nb091_alpha_dummy_197 D R) from (by
          unfold nb091_alpha_dummy_197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0192
                    D R)
                  0)))) (show (nb091_alpha_dummy_193 D R p) ≠ (nb091_alpha_dummy_200 D R p) from
        (by
          unfold nb091_alpha_dummy_200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0193
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_191 D R) ≠
        (nb091_alpha_dummy_195 D R) from (by
          unfold nb091_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0190
                    D R)
                  0)))) (show (nb091_alpha_dummy_193 D R p) ≠ (nb091_alpha_dummy_196 D R p) from
        (by
          unfold nb091_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0191
                    D R p)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_199 D R), (nb091_alpha_dummy_202 D R p)),
        ((nb091_alpha_dummy_198 D R), (nb091_alpha_dummy_201 D R p)),
        ((nb091_alpha_dummy_197 D R), (nb091_alpha_dummy_200 D R p)),
        ((nb091_alpha_dummy_195 D R), (nb091_alpha_dummy_196 D R p)),
        ((nb091_alpha_dummy_191 D R), (nb091_alpha_dummy_193 D R p)),
        ((nb091_alpha_dummy_192 D R), (nb091_alpha_dummy_194 D R p)),
        ((nb091_alpha_dummy_184 D R), (nb091_alpha_dummy_186 D R p)),
        ((nb091_alpha_dummy_183 D R), (nb091_alpha_dummy_185 D R p)),
        ((nb091_alpha_dummy_189 D R), (nb091_alpha_dummy_190 D R p)),
        ((nb091_alpha_dummy_187 D R), (nb091_alpha_dummy_188 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_198 D R) ≠ (nb091_alpha_dummy_205 D R) from
        (by
          unfold
            nb091_alpha_dummy_205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0196
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_201 D R p) ≠ (nb091_alpha_dummy_206 D R p) from
        (by
          unfold
            nb091_alpha_dummy_206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0197
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_198 D R) ≠
        (nb091_alpha_dummy_203 D R) from (by
          unfold
            nb091_alpha_dummy_203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0194
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_201 D R p) ≠ (nb091_alpha_dummy_204 D R p) from
        (by
          unfold
            nb091_alpha_dummy_204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0195
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_191
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_193 D R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_199
        D R) ≠ (nb091_alpha_dummy_205 D R) from (by
          unfold
            nb091_alpha_dummy_205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0200
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_202 D R p) ≠ (nb091_alpha_dummy_206 D R p) from
        (by
          unfold
            nb091_alpha_dummy_206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0201
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_199 D R) ≠
        (nb091_alpha_dummy_203 D R) from (by
          unfold
            nb091_alpha_dummy_203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0198
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_202 D R p) ≠ (nb091_alpha_dummy_204 D R p) from
        (by
          unfold
            nb091_alpha_dummy_204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0199
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_198 D R) ≠ (nb091_alpha_dummy_205 D R) from
        (by
          unfold
            nb091_alpha_dummy_205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0196
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_201 D R p) ≠ (nb091_alpha_dummy_206 D R p) from
        (by
          unfold
            nb091_alpha_dummy_206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0197
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_198 D R) ≠
        (nb091_alpha_dummy_203 D R) from (by
          unfold
            nb091_alpha_dummy_203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0194
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_201 D R p) ≠ (nb091_alpha_dummy_204 D R p) from
        (by
          unfold
            nb091_alpha_dummy_204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0195
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_191
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_193 D R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_199
        D R) ≠ (nb091_alpha_dummy_205 D R) from (by
          unfold
            nb091_alpha_dummy_205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0200
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_202 D R p) ≠ (nb091_alpha_dummy_206 D R p) from
        (by
          unfold
            nb091_alpha_dummy_206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0201
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_199 D R) ≠
        (nb091_alpha_dummy_203 D R) from (by
          unfold
            nb091_alpha_dummy_203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0198
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_202 D R p) ≠ (nb091_alpha_dummy_204 D R p) from
        (by
          unfold
            nb091_alpha_dummy_204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0199
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_199 D R), (nb091_alpha_dummy_202 D R p)),
        ((nb091_alpha_dummy_198 D R), (nb091_alpha_dummy_201 D R p)),
        ((nb091_alpha_dummy_197 D R), (nb091_alpha_dummy_200 D R p)),
        ((nb091_alpha_dummy_195 D R), (nb091_alpha_dummy_196 D R p)),
        ((nb091_alpha_dummy_191 D R), (nb091_alpha_dummy_193 D R p)),
        ((nb091_alpha_dummy_192 D R), (nb091_alpha_dummy_194 D R p)),
        ((nb091_alpha_dummy_184 D R), (nb091_alpha_dummy_186 D R p)),
        ((nb091_alpha_dummy_183 D R), (nb091_alpha_dummy_185 D R p)),
        ((nb091_alpha_dummy_189 D R), (nb091_alpha_dummy_190 D R p)),
        ((nb091_alpha_dummy_187 D R), (nb091_alpha_dummy_188 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_191 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_193 D R p))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_191 D R))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_193
        D R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_198 D R) ≠ (nb091_alpha_dummy_209 D R) from
        (by
          unfold
            nb091_alpha_dummy_209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0204
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_201 D R p) ≠ (nb091_alpha_dummy_210 D R p) from
        (by
          unfold
            nb091_alpha_dummy_210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0205
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_198 D R) ≠
        (nb091_alpha_dummy_207 D R) from (by
          unfold
            nb091_alpha_dummy_207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0202
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_201 D R p) ≠ (nb091_alpha_dummy_208 D R p) from
        (by
          unfold
            nb091_alpha_dummy_208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0203
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_191
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_193 D R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_198
        D R) ≠ (nb091_alpha_dummy_209 D R) from (by
          unfold
            nb091_alpha_dummy_209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0204
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_201 D R p) ≠ (nb091_alpha_dummy_210 D R p) from
        (by
          unfold
            nb091_alpha_dummy_210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0205
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_198 D R) ≠
        (nb091_alpha_dummy_207 D R) from (by
          unfold
            nb091_alpha_dummy_207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0202
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_201 D R p) ≠ (nb091_alpha_dummy_208 D R p) from
        (by
          unfold
            nb091_alpha_dummy_208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0203
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_191
        D R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_193 D R p))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_199 D R) ≠ (nb091_alpha_dummy_211 D R) from
        (by
          unfold
            nb091_alpha_dummy_211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0208
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_202 D R p) ≠ (nb091_alpha_dummy_212 D R p) from
        (by
          unfold
            nb091_alpha_dummy_212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0209
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_199 D R) ≠
        (nb091_alpha_dummy_207 D R) from (by
          unfold
            nb091_alpha_dummy_207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0206
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_202 D R p) ≠ (nb091_alpha_dummy_208 D R p) from
        (by
          unfold
            nb091_alpha_dummy_208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0207
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_199
        D R) ≠ (nb091_alpha_dummy_211 D R) from (by
          unfold
            nb091_alpha_dummy_211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0208
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_202 D R p) ≠ (nb091_alpha_dummy_212 D R p) from
        (by
          unfold
            nb091_alpha_dummy_212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0209
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_199 D R) ≠
        (nb091_alpha_dummy_207 D R) from (by
          unfold
            nb091_alpha_dummy_207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0206
                    D
                    R)
                  0)))) (show (nb091_alpha_dummy_202 D R p) ≠ (nb091_alpha_dummy_208 D R p) from
        (by
          unfold
            nb091_alpha_dummy_208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0207
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb091_alpha_dummy_191 D R) ≠ (nb091_alpha_dummy_195 D R) from (by
          unfold nb091_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0190 D R) 0)))) (show (nb091_alpha_dummy_193 D R p) ≠
        (nb091_alpha_dummy_196 D R p) from (by
          unfold nb091_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0191 D R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_195 D R), (nb091_alpha_dummy_196 D R p)),
        ((nb091_alpha_dummy_191 D R), (nb091_alpha_dummy_193 D R p)),
        ((nb091_alpha_dummy_192 D R), (nb091_alpha_dummy_194 D R p)),
        ((nb091_alpha_dummy_184 D R), (nb091_alpha_dummy_186 D R p)),
        ((nb091_alpha_dummy_183 D R), (nb091_alpha_dummy_185 D R p)),
        ((nb091_alpha_dummy_189 D R), (nb091_alpha_dummy_190 D R p)),
        ((nb091_alpha_dummy_187 D R), (nb091_alpha_dummy_188 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb091_alpha_dummy_191 D R) ≠
        (nb091_alpha_dummy_195 D R) from (by
          unfold nb091_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0190 D R) 0)))) (show (nb091_alpha_dummy_193 D R p) ≠
        (nb091_alpha_dummy_196 D R p) from (by
          unfold nb091_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0191 D R p) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb091_alpha_dummy_191 D R) ≠ (nb091_alpha_dummy_195 D R) from (by
          unfold nb091_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0190 D R) 0)))) (show (nb091_alpha_dummy_193 D R p) ≠
        (nb091_alpha_dummy_196 D R p) from (by
          unfold nb091_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0191 D R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_195 D R), (nb091_alpha_dummy_196 D R p)),
        ((nb091_alpha_dummy_191 D R), (nb091_alpha_dummy_193 D R p)),
        ((nb091_alpha_dummy_192 D R), (nb091_alpha_dummy_194 D R p)),
        ((nb091_alpha_dummy_184 D R), (nb091_alpha_dummy_186 D R p)),
        ((nb091_alpha_dummy_183 D R), (nb091_alpha_dummy_185 D R p)),
        ((nb091_alpha_dummy_189 D R), (nb091_alpha_dummy_190 D R p)),
        ((nb091_alpha_dummy_187 D R), (nb091_alpha_dummy_188 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_cnnc)
        (by simp only [fv_syn_cnnc])))))))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb091_split_alpha_0013 D R p)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb091_split_alpha_0013 D R p)))))))))))

theorem nb091_wpp_notmem_0578 (D : Class) (R : Class) :
    (nb091_alpha_dummy_042 D R) ∉ ((syn_chwniso D)).fv := by
  simpa only [nb091_alpha_dummy_042, fv_syn_chwniso] using (nb091_focused_notmem_0052 D R)

theorem nb091_wpp_notmem_0579 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_044 D R p) ∉ ((syn_chwniso D)).fv := by
  simpa only [nb091_alpha_dummy_044, fv_syn_chwniso] using
    (nb091_focused_notmem_0053 D R p)

theorem nb091_wpp_notmem_0580 (D : Class) (R : Class) :
    (nb091_alpha_dummy_041 D R) ∉ ((syn_chwniso D)).fv := by
  simpa only [nb091_alpha_dummy_041, fv_syn_chwniso] using (nb091_focused_notmem_0054 D R)

theorem nb091_wpp_notmem_0581 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_043 D R p) ∉ ((syn_chwniso D)).fv := by
  simpa only [nb091_alpha_dummy_043, fv_syn_chwniso] using
    (nb091_focused_notmem_0055 D R p)

theorem nb091_wpp_notmem_0582 (D : Class) (R : Class) :
    (nb091_alpha_dummy_001 D R) ∉ ((syn_chwniso D)).fv := by
  simpa only [nb091_alpha_dummy_001, fv_syn_chwniso] using (nb091_focused_notmem_0000 D R)

theorem nb091_wpp_notmem_0583 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_002 D R p) ∉ ((syn_chwniso D)).fv := by
  simpa only [nb091_alpha_dummy_002, fv_syn_chwniso] using
    (nb091_focused_notmem_0001 D R p)

theorem nb091_wpp_notmem_0584 (D : Class) (R : Class) :
    (nb091_alpha_dummy_000 D R) ∉ ((syn_chwniso D)).fv := by
  simpa only [nb091_alpha_dummy_000, fv_syn_chwniso] using (nb091_focused_notmem_0002 D R)

theorem nb091_wpp_notmem_0585 (D : Class) (p : Var) (dv_D_p : p ∉ D.fv) :
    p ∉ ((syn_chwniso D)).fv := by simpa only [fv_syn_chwniso] using dv_D_p

theorem nb091_wpp_notmem_0586 (D : Class) (R : Class) :
    (nb091_alpha_dummy_003 D R) ∉ ((syn_chwniso D)).fv := by
  simpa only [nb091_alpha_dummy_003, fv_syn_chwniso] using (nb091_focused_notmem_0003 D R)

theorem nb091_wpp_notmem_0587 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_004 D R p) ∉ ((syn_chwniso D)).fv := by
  simpa only [nb091_alpha_dummy_004, fv_syn_chwniso] using
    (nb091_focused_notmem_0004 D R p)

theorem nb091_compact_envfresh_0048 (D : Class) (R : Class) (p : Var)
    (dv_D_p : p ∉ D.fv) :
    TEnvFresh
      [((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p),
        ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))]
      ((syn_chwniso D)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb091_alpha_dummy_042 D R) (nb091_alpha_dummy_044 D R p)
      (nb091_wpp_notmem_0578 D R) (nb091_wpp_notmem_0579 D R p)
      (TEnvFresh.consFresh (nb091_alpha_dummy_041 D R) (nb091_alpha_dummy_043 D R p)
        (nb091_wpp_notmem_0580 D R) (nb091_wpp_notmem_0581 D R p)
        (TEnvFresh.consFresh (nb091_alpha_dummy_001 D R) (nb091_alpha_dummy_002 D R p)
          (nb091_wpp_notmem_0582 D R) (nb091_wpp_notmem_0583 D R p)
          (TEnvFresh.consFresh (nb091_alpha_dummy_000 D R) p (nb091_wpp_notmem_0584 D R)
            (nb091_wpp_notmem_0585 D p dv_D_p)
            (TEnvFresh.consFresh (nb091_alpha_dummy_003 D R) (nb091_alpha_dummy_004 D R p)
              (nb091_wpp_notmem_0586 D R) (nb091_wpp_notmem_0587 D R p)
              (TEnvFresh.nil ((syn_chwniso D)).fv))))))

@[expose]
noncomputable def nb091_wpp_refl_0045 (D : Class) (R : Class) (p : Var)
    (dv_D_p : p ∉ D.fv) :
    TReflOn
      [((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p),
        ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))]
      ((syn_chwniso D)).fv :=
  TEnvFresh.reflOn (nb091_compact_envfresh_0048 D R p dv_D_p)

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
noncomputable def nominal_df_hnwcutmap (D : Class) (R : Class) (p : Var)
    (dv_D_p : p ∉ D.fv) (dv_R_p : p ∉ R.fv) :
    Nominal.NPrf
      (.classEq (syn_chnwcutmap R D) (syn_cmpt p (syn_cpw1 (syn_cpw1 D))
          (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso D)))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
            (TAlphaWff.conj (nb091_split_alpha_0002 D R p) (TAlphaWff.conj (TAlphaWff.classMem
                  (TAlphaClass.cv (TAlphaVar.there
                      (show (nb091_alpha_dummy_000 D R) ≠ (nb091_alpha_dummy_001 D R) from (by
                          unfold nb091_alpha_dummy_001;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0004 D R) 0))))
                      (show p ≠ (nb091_alpha_dummy_002 D R p) from (by
                          unfold nb091_alpha_dummy_002;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0005 D R p) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn
                    [((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
                      ((nb091_alpha_dummy_000 D R), p),
                      ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))]
                    (syn_cpw1 (syn_cpw1 D)) (nb091_wpp_refl_0007 D R p dv_D_p)))
                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.neg (nb091_split_alpha_0008 D R p dv_D_p dv_R_p)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.neg (nb091_split_alpha_0008 D R p dv_D_p dv_R_p)))))))))
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb091_split_alpha_0012 D R p dv_D_p dv_R_p))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cab (TAlphaWff.neg
                              (TAlphaWff.neg (nb091_split_alpha_0014 D R p))))
                          (TAlphaClass.refl_of_reflOn
                            [((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
                              ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
                              ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
                              ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
                                (nb091_alpha_dummy_004 D R p))]
                            (syn_chwniso D) (nb091_wpp_refl_0045 D R p dv_D_p))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
