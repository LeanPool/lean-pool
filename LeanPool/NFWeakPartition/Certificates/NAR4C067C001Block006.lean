/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C067C001Block005

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C067C001Part026`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0057`. -/
@[expose]
noncomputable def nb067SplitAlpha0057 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy213), (nb067AlphaDummy215 f)),
        ((nb067AlphaDummy214), (nb067AlphaDummy216 f)),
        ((nb067AlphaDummy239), (nb067AlphaDummy240 f)),
        ((nb067AlphaDummy237), (nb067AlphaDummy238 f)),
        ((nb067AlphaDummy206), (nb067AlphaDummy208 f)),
        ((nb067AlphaDummy205), (nb067AlphaDummy207 f)),
        ((nb067AlphaDummy235), (nb067AlphaDummy236 f)),
        ((nb067AlphaDummy209), (nb067AlphaDummy210 f)),
        ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
        ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
        ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.classEq (Class.cv (nb067AlphaDummy214))
        (synCif (Wff.classMem (Class.cv (nb067AlphaDummy213)) (synCnnc))
          (synCplc (Class.cv (nb067AlphaDummy213)) (synC1c))
          (Class.cv (nb067AlphaDummy213))))
      (Wff.classEq (Class.cv (nb067AlphaDummy216 f))
        (synCif (Wff.classMem (Class.cv (nb067AlphaDummy215 f)) (synCnnc))
          (synCplc (Class.cv (nb067AlphaDummy215 f)) (synC1c))
          (Class.cv (nb067AlphaDummy215 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb067AlphaDummy206))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb067AlphaDummy208 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy213) ≠ (nb067AlphaDummy220) from (by
                              unfold nb067AlphaDummy220;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0224) 1))))
                          (show (nb067AlphaDummy215 f) ≠ (nb067AlphaDummy223 f) from (by
                              unfold nb067AlphaDummy223;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0225 f) 1))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy213) ≠ (nb067AlphaDummy219) from (by
                                unfold nb067AlphaDummy219;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0224) 0))))
                            (show (nb067AlphaDummy215 f) ≠ (nb067AlphaDummy222 f) from (by
                                unfold nb067AlphaDummy222;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0225 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy213) ≠ (nb067AlphaDummy217) from (by
                                  unfold nb067AlphaDummy217;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0222) 0))))
                              (show (nb067AlphaDummy215 f) ≠ (nb067AlphaDummy218 f) from
                                (by
                                  unfold nb067AlphaDummy218;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0223 f) 0))))
                              (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.reflOfClosed
                            [((nb067AlphaDummy221), (nb067AlphaDummy224 f)),
                              ((nb067AlphaDummy220), (nb067AlphaDummy223 f)),
                              ((nb067AlphaDummy219), (nb067AlphaDummy222 f)),
                              ((nb067AlphaDummy217), (nb067AlphaDummy218 f)),
                              ((nb067AlphaDummy213), (nb067AlphaDummy215 f)),
                              ((nb067AlphaDummy214), (nb067AlphaDummy216 f)),
                              ((nb067AlphaDummy239), (nb067AlphaDummy240 f)),
                              ((nb067AlphaDummy237), (nb067AlphaDummy238 f)),
                              ((nb067AlphaDummy206), (nb067AlphaDummy208 f)),
                              ((nb067AlphaDummy205), (nb067AlphaDummy207 f)),
                              ((nb067AlphaDummy235), (nb067AlphaDummy236 f)),
                              ((nb067AlphaDummy209), (nb067AlphaDummy210 f)),
                              ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
                              ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
                              ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
                              ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                              ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                              ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                              ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                              ((nb067AlphaDummy000), f),
                              ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                              ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                              ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                            (synC1c) (by simp only [fv_syn_c1c])))
                        (TAlphaWff.neg (nb067SplitAlpha0056 x y f)))))))) (TAlphaWff.classMem
              (TAlphaClass.cv (TAlphaVar.there
                  (show (nb067AlphaDummy213) ≠ (nb067AlphaDummy217) from (by
                      unfold nb067AlphaDummy217;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0222) 0))))
                  (show (nb067AlphaDummy215 f) ≠ (nb067AlphaDummy218 f) from (by
                      unfold nb067AlphaDummy218;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0223 f) 0))))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                [((nb067AlphaDummy217), (nb067AlphaDummy218 f)),
                  ((nb067AlphaDummy213), (nb067AlphaDummy215 f)),
                  ((nb067AlphaDummy214), (nb067AlphaDummy216 f)),
                  ((nb067AlphaDummy239), (nb067AlphaDummy240 f)),
                  ((nb067AlphaDummy237), (nb067AlphaDummy238 f)),
                  ((nb067AlphaDummy206), (nb067AlphaDummy208 f)),
                  ((nb067AlphaDummy205), (nb067AlphaDummy207 f)),
                  ((nb067AlphaDummy235), (nb067AlphaDummy236 f)),
                  ((nb067AlphaDummy209), (nb067AlphaDummy210 f)),
                  ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
                  ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
                  ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
                  ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                  ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                  ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                  ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                  ((nb067AlphaDummy000), f),
                  ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                  ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                  ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (show (nb067AlphaDummy213) ≠ (nb067AlphaDummy217) from (by
                    unfold nb067AlphaDummy217;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0222) 0))))
                (show (nb067AlphaDummy215 f) ≠ (nb067AlphaDummy218 f) from (by
                    unfold nb067AlphaDummy218;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0223 f) 0))))
                (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                (TAlphaVar.there (show (nb067AlphaDummy213) ≠ (nb067AlphaDummy217) from
                    (by
                      unfold nb067AlphaDummy217;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0222) 0))))
                  (show (nb067AlphaDummy215 f) ≠ (nb067AlphaDummy218 f) from (by
                      unfold nb067AlphaDummy218;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0223 f) 0))))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                [((nb067AlphaDummy217), (nb067AlphaDummy218 f)),
                  ((nb067AlphaDummy213), (nb067AlphaDummy215 f)),
                  ((nb067AlphaDummy214), (nb067AlphaDummy216 f)),
                  ((nb067AlphaDummy239), (nb067AlphaDummy240 f)),
                  ((nb067AlphaDummy237), (nb067AlphaDummy238 f)),
                  ((nb067AlphaDummy206), (nb067AlphaDummy208 f)),
                  ((nb067AlphaDummy205), (nb067AlphaDummy207 f)),
                  ((nb067AlphaDummy235), (nb067AlphaDummy236 f)),
                  ((nb067AlphaDummy209), (nb067AlphaDummy210 f)),
                  ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
                  ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
                  ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
                  ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                  ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                  ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                  ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                  ((nb067AlphaDummy000), f),
                  ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                  ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                  ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                (synCnnc) (by simp only [fv_syn_cnnc]))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0058`. -/
@[expose]
noncomputable def nb067SplitAlpha0058 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy235), (nb067AlphaDummy236 f)),
        ((nb067AlphaDummy209), (nb067AlphaDummy210 f)),
        ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
        ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
        ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy235))
          (Class.cab (nb067AlphaDummy205)
            (synWrex (nb067AlphaDummy206) (Class.cv (nb067AlphaDummy163))
              (Wff.classEq (Class.cv (nb067AlphaDummy205))
                (synCun (synCphi (Class.cv (nb067AlphaDummy206))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb067AlphaDummy235))
            (Class.cab (nb067AlphaDummy205)
              (synWrex (nb067AlphaDummy206) (Class.cv (nb067AlphaDummy163))
                (Wff.classEq (Class.cv (nb067AlphaDummy205))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy206)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy236 f))
          (Class.cab (nb067AlphaDummy207 f)
            (synWrex (nb067AlphaDummy208 f) (Class.cv (nb067AlphaDummy165 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy207 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy208 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb067AlphaDummy236 f))
            (Class.cab (nb067AlphaDummy207 f)
              (synWrex (nb067AlphaDummy208 f) (Class.cv (nb067AlphaDummy165 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy207 f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy208 f)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb067AlphaDummy163) ≠ (nb067AlphaDummy206) from
                    (by
                      unfold nb067AlphaDummy206;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0242) 1))))
                  (show (nb067AlphaDummy165 f) ≠ (nb067AlphaDummy208 f) from (by
                      unfold nb067AlphaDummy208;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0244 f) 1))))
                  (TAlphaVar.there (show (nb067AlphaDummy163) ≠ (nb067AlphaDummy205) from
                      (by
                        unfold nb067AlphaDummy205;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0242) 0))))
                    (show (nb067AlphaDummy165 f) ≠ (nb067AlphaDummy207 f) from (by
                        unfold nb067AlphaDummy207;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0244 f) 0)))) (TAlphaVar.there
                      (show (nb067AlphaDummy163) ≠ (nb067AlphaDummy235) from (by
                          unfold nb067AlphaDummy235;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0246) 0))))
                      (show (nb067AlphaDummy165 f) ≠ (nb067AlphaDummy236 f) from (by
                          unfold nb067AlphaDummy236;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0247 f) 0))))
                      (TAlphaVar.there
                        (show (nb067AlphaDummy163) ≠ (nb067AlphaDummy209) from (by
                            unfold nb067AlphaDummy209;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0243) 0))))
                        (show (nb067AlphaDummy165 f) ≠ (nb067AlphaDummy210 f) from (by
                            unfold nb067AlphaDummy210;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0245 f) 0))))
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb067AlphaDummy000))).fv)
                            (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb067AlphaDummy164))).fv ∪
                      ((Class.cv (nb067AlphaDummy163))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb067AlphaDummy166 f))).fv ∪
                      ((Class.cv (nb067AlphaDummy165 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb067AlphaDummy206) ≠
        (nb067AlphaDummy213) from (by
          unfold nb067AlphaDummy213;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0220) 0)))) (show (nb067AlphaDummy208 f) ≠
        (nb067AlphaDummy215 f) from (by
          unfold nb067AlphaDummy215;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0221 f) 0)))) (TAlphaVar.there (show
        (nb067AlphaDummy206) ≠ (nb067AlphaDummy214) from (by
          unfold nb067AlphaDummy214;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0220) 1)))) (show (nb067AlphaDummy208 f) ≠
        (nb067AlphaDummy216 f) from (by
          unfold nb067AlphaDummy216;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0221 f) 1)))) (TAlphaVar.there (show
        (nb067AlphaDummy206) ≠ (nb067AlphaDummy239) from (by
          unfold nb067AlphaDummy239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0250) 0)))) (show (nb067AlphaDummy208 f) ≠
        (nb067AlphaDummy240 f) from (by
          unfold nb067AlphaDummy240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0251 f) 0)))) (TAlphaVar.there (show
        (nb067AlphaDummy206) ≠ (nb067AlphaDummy237) from (by
          unfold nb067AlphaDummy237;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0248) 0)))) (show (nb067AlphaDummy208 f) ≠
        (nb067AlphaDummy238 f) from (by
          unfold nb067AlphaDummy238;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0249 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb067SplitAlpha0057 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb067AlphaDummy206) ≠
        (nb067AlphaDummy213) from (by
          unfold nb067AlphaDummy213;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0220) 0)))) (show (nb067AlphaDummy208 f) ≠
        (nb067AlphaDummy215 f) from (by
          unfold nb067AlphaDummy215;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0221 f) 0)))) (TAlphaVar.there (show
        (nb067AlphaDummy206) ≠ (nb067AlphaDummy214) from (by
          unfold nb067AlphaDummy214;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0220) 1)))) (show (nb067AlphaDummy208 f) ≠
        (nb067AlphaDummy216 f) from (by
          unfold nb067AlphaDummy216;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0221 f) 1)))) (TAlphaVar.there (show
        (nb067AlphaDummy206) ≠ (nb067AlphaDummy239) from (by
          unfold nb067AlphaDummy239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0250) 0)))) (show (nb067AlphaDummy208 f) ≠
        (nb067AlphaDummy240 f) from (by
          unfold nb067AlphaDummy240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0251 f) 0)))) (TAlphaVar.there (show
        (nb067AlphaDummy206) ≠ (nb067AlphaDummy237) from (by
          unfold nb067AlphaDummy237;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0248) 0)))) (show (nb067AlphaDummy208 f) ≠
        (nb067AlphaDummy238 f) from (by
          unfold nb067AlphaDummy238;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0249 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb067SplitAlpha0057 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb067AlphaDummy237), (nb067AlphaDummy238 f)),
                          ((nb067AlphaDummy206), (nb067AlphaDummy208 f)),
                          ((nb067AlphaDummy205), (nb067AlphaDummy207 f)),
                          ((nb067AlphaDummy235), (nb067AlphaDummy236 f)),
                          ((nb067AlphaDummy209), (nb067AlphaDummy210 f)),
                          ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
                          ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
                          ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
                          ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                          ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                          ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                          ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                          ((nb067AlphaDummy000), f),
                          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067AlphaDummy163) ≠ (nb067AlphaDummy206) from
                      (by
                        unfold nb067AlphaDummy206;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0242) 1))))
                    (show (nb067AlphaDummy165 f) ≠ (nb067AlphaDummy208 f) from (by
                        unfold nb067AlphaDummy208;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0244 f) 1)))) (TAlphaVar.there
                      (show (nb067AlphaDummy163) ≠ (nb067AlphaDummy205) from (by
                          unfold nb067AlphaDummy205;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0242) 0))))
                      (show (nb067AlphaDummy165 f) ≠ (nb067AlphaDummy207 f) from (by
                          unfold nb067AlphaDummy207;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0244 f) 0))))
                      (TAlphaVar.there
                        (show (nb067AlphaDummy163) ≠ (nb067AlphaDummy235) from (by
                            unfold nb067AlphaDummy235;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0246) 0))))
                        (show (nb067AlphaDummy165 f) ≠ (nb067AlphaDummy236 f) from (by
                            unfold nb067AlphaDummy236;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0247 f) 0))))
                        (TAlphaVar.there
                          (show (nb067AlphaDummy163) ≠ (nb067AlphaDummy209) from (by
                              unfold nb067AlphaDummy209;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0243) 0))))
                          (show (nb067AlphaDummy165 f) ≠ (nb067AlphaDummy210 f) from (by
                              unfold nb067AlphaDummy210;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0245 f) 0))))
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb067AlphaDummy000))).fv)
                              (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb067AlphaDummy164))).fv ∪
                        ((Class.cv (nb067AlphaDummy163))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb067AlphaDummy166 f))).fv ∪
                        ((Class.cv (nb067AlphaDummy165 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067AlphaDummy206) ≠ (nb067AlphaDummy213) from (by
          unfold nb067AlphaDummy213;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0220) 0)))) (show (nb067AlphaDummy208 f) ≠
        (nb067AlphaDummy215 f) from (by
          unfold nb067AlphaDummy215;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0221 f) 0)))) (TAlphaVar.there (show
        (nb067AlphaDummy206) ≠ (nb067AlphaDummy214) from (by
          unfold nb067AlphaDummy214;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0220) 1)))) (show (nb067AlphaDummy208 f) ≠
        (nb067AlphaDummy216 f) from (by
          unfold nb067AlphaDummy216;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0221 f) 1)))) (TAlphaVar.there (show
        (nb067AlphaDummy206) ≠ (nb067AlphaDummy239) from (by
          unfold nb067AlphaDummy239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0250) 0)))) (show (nb067AlphaDummy208 f) ≠
        (nb067AlphaDummy240 f) from (by
          unfold nb067AlphaDummy240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0251 f)
                  0)))) (TAlphaVar.there (show (nb067AlphaDummy206) ≠ (nb067AlphaDummy237)
        from (by
          unfold nb067AlphaDummy237;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0248)
                  0)))) (show (nb067AlphaDummy208 f) ≠ (nb067AlphaDummy238 f) from (by
          unfold nb067AlphaDummy238;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0249 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb067SplitAlpha0057 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067AlphaDummy206) ≠ (nb067AlphaDummy213) from (by
          unfold nb067AlphaDummy213;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0220) 0)))) (show (nb067AlphaDummy208 f) ≠
        (nb067AlphaDummy215 f) from (by
          unfold nb067AlphaDummy215;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0221 f) 0)))) (TAlphaVar.there (show
        (nb067AlphaDummy206) ≠ (nb067AlphaDummy214) from (by
          unfold nb067AlphaDummy214;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0220) 1)))) (show (nb067AlphaDummy208 f) ≠
        (nb067AlphaDummy216 f) from (by
          unfold nb067AlphaDummy216;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0221 f) 1)))) (TAlphaVar.there (show
        (nb067AlphaDummy206) ≠ (nb067AlphaDummy239) from (by
          unfold nb067AlphaDummy239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0250) 0)))) (show (nb067AlphaDummy208 f) ≠
        (nb067AlphaDummy240 f) from (by
          unfold nb067AlphaDummy240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0251 f)
                  0)))) (TAlphaVar.there (show (nb067AlphaDummy206) ≠ (nb067AlphaDummy237)
        from (by
          unfold nb067AlphaDummy237;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0248)
                  0)))) (show (nb067AlphaDummy208 f) ≠ (nb067AlphaDummy238 f) from (by
          unfold nb067AlphaDummy238;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0249 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb067SplitAlpha0057 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb067AlphaDummy237), (nb067AlphaDummy238 f)),
                            ((nb067AlphaDummy206), (nb067AlphaDummy208 f)),
                            ((nb067AlphaDummy205), (nb067AlphaDummy207 f)),
                            ((nb067AlphaDummy235), (nb067AlphaDummy236 f)),
                            ((nb067AlphaDummy209), (nb067AlphaDummy210 f)),
                            ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
                            ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
                            ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
                            ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                            ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                            ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                            ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                            ((nb067AlphaDummy000), f),
                            ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                            ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                            ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0059`. -/
@[expose]
noncomputable def nb067SplitAlpha0059 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
        ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
        ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classEq (Class.cv (nb067AlphaDummy167))
          (synCop (Class.cv (nb067AlphaDummy163)) (Class.cv (nb067AlphaDummy164))))
        (Wff.neg (synWbr (Class.cv (nb067AlphaDummy164)) (Class.cv (nb067AlphaDummy000))
            (Class.cv (nb067AlphaDummy163)))))
      (Wff.imp (Wff.classEq (Class.cv (nb067AlphaDummy168 f))
          (synCop (Class.cv (nb067AlphaDummy165 f)) (Class.cv (nb067AlphaDummy166 f))))
        (Wff.neg (synWbr (Class.cv (nb067AlphaDummy166 f)) (Class.cv f)
            (Class.cv (nb067AlphaDummy165 f))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
            (show (nb067AlphaDummy164) ≠ (nb067AlphaDummy167) from (by
                unfold nb067AlphaDummy167;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0174) 0))))) (Ne.symm
            (show (nb067AlphaDummy166 f) ≠ (nb067AlphaDummy168 f) from (by
                unfold nb067AlphaDummy168;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0175 f) 0)))))
          (TAlphaVar.there (Ne.symm (show (nb067AlphaDummy163) ≠ (nb067AlphaDummy167) from
                (by
                  unfold nb067AlphaDummy167;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0172) 0)))))
            (Ne.symm (show (nb067AlphaDummy165 f) ≠ (nb067AlphaDummy168 f) from (by
                  unfold nb067AlphaDummy168;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0173 f) 0)))))
            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb067AlphaDummy163) ≠ (nb067AlphaDummy170) from
                                    (by
                                      unfold nb067AlphaDummy170;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0176)
                                              1)))) (show
                                    (nb067AlphaDummy165 f) ≠ (nb067AlphaDummy172 f) from
                                    (by
                                      unfold nb067AlphaDummy172;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0178 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb067AlphaDummy163) ≠ (nb067AlphaDummy169) from (by
                                        unfold nb067AlphaDummy169;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0176)
                                                0)))) (show (nb067AlphaDummy165 f) ≠
                                        (nb067AlphaDummy171 f) from (by
                                        unfold nb067AlphaDummy171;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0178 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb067AlphaDummy163) ≠ (nb067AlphaDummy175) from
                                        (by
                                          unfold nb067AlphaDummy175;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb067_support_mem_0180)
                                                  0)))) (show (nb067AlphaDummy165 f) ≠
        (nb067AlphaDummy176 f) from (by
                                          unfold nb067AlphaDummy176;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb067_support_mem_0181 f) 0))))
                                      (TAlphaVar.there (show (nb067AlphaDummy163) ≠
        (nb067AlphaDummy173) from (by
          unfold nb067AlphaDummy173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0177) 0)))) (show (nb067AlphaDummy165 f) ≠
        (nb067AlphaDummy174 f) from (by
          unfold nb067AlphaDummy174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0179 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb067AlphaDummy000))).fv) (by decide))
        (freshVar_injective (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb067AlphaDummy163))).fv ∪
                                      ((Class.cv (nb067AlphaDummy164))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb067AlphaDummy165 f))).fv ∪
                                      ((Class.cv (nb067AlphaDummy166 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067SplitAlpha0050 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb067AlphaDummy163) ≠ (nb067AlphaDummy170) from
                                    (by
                                      unfold nb067AlphaDummy170;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0176)
                                              1)))) (show
                                    (nb067AlphaDummy165 f) ≠ (nb067AlphaDummy172 f) from
                                    (by
                                      unfold nb067AlphaDummy172;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0178 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb067AlphaDummy163) ≠ (nb067AlphaDummy169) from (by
                                        unfold nb067AlphaDummy169;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0176)
                                                0)))) (show (nb067AlphaDummy165 f) ≠
                                        (nb067AlphaDummy171 f) from (by
                                        unfold nb067AlphaDummy171;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0178 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb067AlphaDummy163) ≠ (nb067AlphaDummy175) from
                                        (by
                                          unfold nb067AlphaDummy175;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb067_support_mem_0180)
                                                  0)))) (show (nb067AlphaDummy165 f) ≠
        (nb067AlphaDummy176 f) from (by
                                          unfold nb067AlphaDummy176;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb067_support_mem_0181 f) 0))))
                                      (TAlphaVar.there (show (nb067AlphaDummy163) ≠
        (nb067AlphaDummy173) from (by
          unfold nb067AlphaDummy173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0177) 0)))) (show (nb067AlphaDummy165 f) ≠
        (nb067AlphaDummy174 f) from (by
          unfold nb067AlphaDummy174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0179 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb067AlphaDummy000))).fv) (by decide))
        (freshVar_injective (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb067AlphaDummy163))).fv ∪
                                      ((Class.cv (nb067AlphaDummy164))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb067AlphaDummy165 f))).fv ∪
                                      ((Class.cv (nb067AlphaDummy166 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067SplitAlpha0050 x y f)))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb067SplitAlpha0053 x y f)))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb067AlphaDummy164) ≠ (nb067AlphaDummy206) from (by
                                        unfold nb067AlphaDummy206;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0214)
                                                1)))) (show (nb067AlphaDummy166 f) ≠
                                        (nb067AlphaDummy208 f) from (by
                                        unfold nb067AlphaDummy208;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0216 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb067AlphaDummy164) ≠ (nb067AlphaDummy205) from
                                        (by
                                          unfold nb067AlphaDummy205;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb067_support_mem_0214)
                                                  0)))) (show (nb067AlphaDummy166 f) ≠
        (nb067AlphaDummy207 f) from (by
                                          unfold nb067AlphaDummy207;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb067_support_mem_0216 f) 0))))
                                      (TAlphaVar.there (show (nb067AlphaDummy164) ≠
        (nb067AlphaDummy211) from (by
          unfold nb067AlphaDummy211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0218) 0)))) (show (nb067AlphaDummy166 f) ≠
        (nb067AlphaDummy212 f) from (by
          unfold nb067AlphaDummy212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0219 f) 0)))) (TAlphaVar.there (show
        (nb067AlphaDummy164) ≠ (nb067AlphaDummy209) from (by
          unfold nb067AlphaDummy209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0215) 0)))) (show (nb067AlphaDummy166 f) ≠
        (nb067AlphaDummy210 f) from (by
          unfold nb067AlphaDummy210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0217 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb067AlphaDummy164))).fv ∪
                                        ((Class.cv (nb067AlphaDummy163))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb067AlphaDummy166 f))).fv ∪
                                        ((Class.cv (nb067AlphaDummy165 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067SplitAlpha0055 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb067AlphaDummy164) ≠ (nb067AlphaDummy206) from (by
                                        unfold nb067AlphaDummy206;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0214)
                                                1)))) (show (nb067AlphaDummy166 f) ≠
                                        (nb067AlphaDummy208 f) from (by
                                        unfold nb067AlphaDummy208;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0216 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb067AlphaDummy164) ≠ (nb067AlphaDummy205) from
                                        (by
                                          unfold nb067AlphaDummy205;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb067_support_mem_0214)
                                                  0)))) (show (nb067AlphaDummy166 f) ≠
        (nb067AlphaDummy207 f) from (by
                                          unfold nb067AlphaDummy207;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb067_support_mem_0216 f) 0))))
                                      (TAlphaVar.there (show (nb067AlphaDummy164) ≠
        (nb067AlphaDummy211) from (by
          unfold nb067AlphaDummy211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0218) 0)))) (show (nb067AlphaDummy166 f) ≠
        (nb067AlphaDummy212 f) from (by
          unfold nb067AlphaDummy212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0219 f) 0)))) (TAlphaVar.there (show
        (nb067AlphaDummy164) ≠ (nb067AlphaDummy209) from (by
          unfold nb067AlphaDummy209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0215) 0)))) (show (nb067AlphaDummy166 f) ≠
        (nb067AlphaDummy210 f) from (by
          unfold nb067AlphaDummy210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0217 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb067AlphaDummy164))).fv ∪
                                        ((Class.cv (nb067AlphaDummy163))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb067AlphaDummy166 f))).fv ∪
                                        ((Class.cv (nb067AlphaDummy165 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067SplitAlpha0055 x y f)))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb067SplitAlpha0058 x y f))))))))
        (TAlphaClass.cv (TAlphaVar.there
            (show (nb067AlphaDummy000) ≠ (nb067AlphaDummy164) from (by
                unfold nb067AlphaDummy164;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0262) 1))))
            (show f ≠ (nb067AlphaDummy166 f) from (by
                unfold nb067AlphaDummy166;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0263 f) 1))))
            (TAlphaVar.there (show (nb067AlphaDummy000) ≠ (nb067AlphaDummy163) from (by
                  unfold nb067AlphaDummy163;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0262) 0))))
              (show f ≠ (nb067AlphaDummy165 f) from (by
                  unfold nb067AlphaDummy165;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0263 f) 0))))
              (TAlphaVar.there (show (nb067AlphaDummy000) ≠ (nb067AlphaDummy167) from (by
                    unfold nb067AlphaDummy167;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0260) 0))))
                (show f ≠ (nb067AlphaDummy168 f) from (by
                    unfold nb067AlphaDummy168;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0261 f) 0))))
                (TAlphaVar.there (show (nb067AlphaDummy000) ≠ (nb067AlphaDummy085) from
                    (by
                      unfold nb067AlphaDummy085;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0256) 2))))
                  (show f ≠ (nb067AlphaDummy088 f) from (by
                      unfold nb067AlphaDummy088;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0258 f) 2))))
                  (TAlphaVar.there (show (nb067AlphaDummy000) ≠ (nb067AlphaDummy084) from
                      (by
                        unfold nb067AlphaDummy084;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0256) 1))))
                    (show f ≠ (nb067AlphaDummy087 f) from (by
                        unfold nb067AlphaDummy087;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0258 f) 1)))) (TAlphaVar.there
                      (show (nb067AlphaDummy000) ≠ (nb067AlphaDummy083) from (by
                          unfold nb067AlphaDummy083;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0256) 0))))
                      (show f ≠ (nb067AlphaDummy086 f) from (by
                          unfold nb067AlphaDummy086;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0258 f) 0))))
                      (TAlphaVar.there
                        (show (nb067AlphaDummy000) ≠ (nb067AlphaDummy089) from (by
                            unfold nb067AlphaDummy089;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0257) 0))))
                        (show f ≠ (nb067AlphaDummy090 f) from (by
                            unfold nb067AlphaDummy090;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0259 f) 0))))
                        (TAlphaVar.here _ _ _))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0060`. -/
@[expose]
noncomputable def nb067SplitAlpha0060 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy257), (nb067AlphaDummy260 f)),
        ((nb067AlphaDummy256), (nb067AlphaDummy259 f)),
        ((nb067AlphaDummy255), (nb067AlphaDummy258 f)),
        ((nb067AlphaDummy253), (nb067AlphaDummy254 f)),
        ((nb067AlphaDummy249), (nb067AlphaDummy251 f)),
        ((nb067AlphaDummy250), (nb067AlphaDummy252 f)),
        ((nb067AlphaDummy242), (nb067AlphaDummy244 f)),
        ((nb067AlphaDummy241), (nb067AlphaDummy243 f)),
        ((nb067AlphaDummy247), (nb067AlphaDummy248 f)),
        ((nb067AlphaDummy245), (nb067AlphaDummy246 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb067AlphaDummy256)) (Class.cv (nb067AlphaDummy257)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb067AlphaDummy255))
            (synCun (Class.cv (nb067AlphaDummy256)) (Class.cv (nb067AlphaDummy257))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb067AlphaDummy259 f))
            (Class.cv (nb067AlphaDummy260 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy258 f))
            (synCun (Class.cv (nb067AlphaDummy259 f))
              (Class.cv (nb067AlphaDummy260 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy256) ≠ (nb067AlphaDummy263) from (by
                              unfold nb067AlphaDummy263;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0278) 0))))
                          (show (nb067AlphaDummy259 f) ≠ (nb067AlphaDummy264 f) from (by
                              unfold nb067AlphaDummy264;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0279 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy256) ≠ (nb067AlphaDummy261) from (by
                                unfold nb067AlphaDummy261;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0276) 0))))
                            (show (nb067AlphaDummy259 f) ≠ (nb067AlphaDummy262 f) from (by
                                unfold nb067AlphaDummy262;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0277 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy249))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy251 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy257) ≠ (nb067AlphaDummy263) from (by
                              unfold nb067AlphaDummy263;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0282) 0))))
                          (show (nb067AlphaDummy260 f) ≠ (nb067AlphaDummy264 f) from (by
                              unfold nb067AlphaDummy264;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0283 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy257) ≠ (nb067AlphaDummy261) from (by
                                unfold nb067AlphaDummy261;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0280) 0))))
                            (show (nb067AlphaDummy260 f) ≠ (nb067AlphaDummy262 f) from (by
                                unfold nb067AlphaDummy262;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0281 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy256) ≠ (nb067AlphaDummy263) from (by
                              unfold nb067AlphaDummy263;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0278) 0))))
                          (show (nb067AlphaDummy259 f) ≠ (nb067AlphaDummy264 f) from (by
                              unfold nb067AlphaDummy264;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0279 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy256) ≠ (nb067AlphaDummy261) from (by
                                unfold nb067AlphaDummy261;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0276) 0))))
                            (show (nb067AlphaDummy259 f) ≠ (nb067AlphaDummy262 f) from (by
                                unfold nb067AlphaDummy262;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0277 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy249))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy251 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy257) ≠ (nb067AlphaDummy263) from (by
                              unfold nb067AlphaDummy263;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0282) 0))))
                          (show (nb067AlphaDummy260 f) ≠ (nb067AlphaDummy264 f) from (by
                              unfold nb067AlphaDummy264;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0283 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy257) ≠ (nb067AlphaDummy261) from (by
                                unfold nb067AlphaDummy261;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0280) 0))))
                            (show (nb067AlphaDummy260 f) ≠ (nb067AlphaDummy262 f) from (by
                                unfold nb067AlphaDummy262;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0281 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb067AlphaDummy257), (nb067AlphaDummy260 f)),
          ((nb067AlphaDummy256), (nb067AlphaDummy259 f)),
          ((nb067AlphaDummy255), (nb067AlphaDummy258 f)),
          ((nb067AlphaDummy253), (nb067AlphaDummy254 f)),
          ((nb067AlphaDummy249), (nb067AlphaDummy251 f)),
          ((nb067AlphaDummy250), (nb067AlphaDummy252 f)),
          ((nb067AlphaDummy242), (nb067AlphaDummy244 f)),
          ((nb067AlphaDummy241), (nb067AlphaDummy243 f)),
          ((nb067AlphaDummy247), (nb067AlphaDummy248 f)),
          ((nb067AlphaDummy245), (nb067AlphaDummy246 f)),
          ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
          ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
          ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
          ((nb067AlphaDummy089), (nb067AlphaDummy090 f)), ((nb067AlphaDummy000), f),
          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy249))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067AlphaDummy251 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067AlphaDummy249))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067AlphaDummy251 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy256) ≠ (nb067AlphaDummy267) from (by
                                unfold nb067AlphaDummy267;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0286) 0))))
                            (show (nb067AlphaDummy259 f) ≠ (nb067AlphaDummy268 f) from (by
                                unfold nb067AlphaDummy268;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0287 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy256) ≠ (nb067AlphaDummy265) from (by
                                  unfold nb067AlphaDummy265;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0284) 0))))
                              (show (nb067AlphaDummy259 f) ≠ (nb067AlphaDummy266 f) from
                                (by
                                  unfold nb067AlphaDummy266;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0285 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy249))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy251 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy256) ≠ (nb067AlphaDummy267) from (by
                                unfold nb067AlphaDummy267;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0286) 0))))
                            (show (nb067AlphaDummy259 f) ≠ (nb067AlphaDummy268 f) from (by
                                unfold nb067AlphaDummy268;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0287 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy256) ≠ (nb067AlphaDummy265) from (by
                                  unfold nb067AlphaDummy265;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0284) 0))))
                              (show (nb067AlphaDummy259 f) ≠ (nb067AlphaDummy266 f) from
                                (by
                                  unfold nb067AlphaDummy266;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0285 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy249))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy251 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy257) ≠ (nb067AlphaDummy269) from (by
                                unfold nb067AlphaDummy269;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0290) 0))))
                            (show (nb067AlphaDummy260 f) ≠ (nb067AlphaDummy270 f) from (by
                                unfold nb067AlphaDummy270;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0291 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy257) ≠ (nb067AlphaDummy265) from (by
                                  unfold nb067AlphaDummy265;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0288) 0))))
                              (show (nb067AlphaDummy260 f) ≠ (nb067AlphaDummy266 f) from
                                (by
                                  unfold nb067AlphaDummy266;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0289 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy257) ≠ (nb067AlphaDummy269) from (by
                                unfold nb067AlphaDummy269;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0290) 0))))
                            (show (nb067AlphaDummy260 f) ≠ (nb067AlphaDummy270 f) from (by
                                unfold nb067AlphaDummy270;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0291 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy257) ≠ (nb067AlphaDummy265) from (by
                                  unfold nb067AlphaDummy265;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0288) 0))))
                              (show (nb067AlphaDummy260 f) ≠ (nb067AlphaDummy266 f) from
                                (by
                                  unfold nb067AlphaDummy266;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0289 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part027`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0061`. -/
@[expose]
noncomputable def nb067SplitAlpha0061 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy249), (nb067AlphaDummy251 f)),
        ((nb067AlphaDummy250), (nb067AlphaDummy252 f)),
        ((nb067AlphaDummy242), (nb067AlphaDummy244 f)),
        ((nb067AlphaDummy241), (nb067AlphaDummy243 f)),
        ((nb067AlphaDummy247), (nb067AlphaDummy248 f)),
        ((nb067AlphaDummy245), (nb067AlphaDummy246 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.neg (synWa (Wff.classMem (Class.cv (nb067AlphaDummy249))
            (Class.cv (nb067AlphaDummy242))) (Wff.classEq (Class.cv (nb067AlphaDummy250))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy249)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy249)) (synC1c))
              (Class.cv (nb067AlphaDummy249))))))
      (Wff.neg (synWa (Wff.classMem (Class.cv (nb067AlphaDummy251 f))
            (Class.cv (nb067AlphaDummy244 f)))
          (Wff.classEq (Class.cv (nb067AlphaDummy252 f))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy251 f)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy251 f)) (synC1c))
              (Class.cv (nb067AlphaDummy251 f)))))) :=
  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there
            (show (nb067AlphaDummy242) ≠ (nb067AlphaDummy249) from (by
                unfold nb067AlphaDummy249;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0270) 0))))
            (show (nb067AlphaDummy244 f) ≠ (nb067AlphaDummy251 f) from (by
                unfold nb067AlphaDummy251;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0271 f) 0))))
            (TAlphaVar.there (show (nb067AlphaDummy242) ≠ (nb067AlphaDummy250) from (by
                  unfold nb067AlphaDummy250;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0270) 1))))
              (show (nb067AlphaDummy244 f) ≠ (nb067AlphaDummy252 f) from (by
                  unfold nb067AlphaDummy252;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0271 f) 1))))
              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy242))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb067AlphaDummy244 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb067AlphaDummy249) ≠ (nb067AlphaDummy256) from (by
                                  unfold nb067AlphaDummy256;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0274) 1))))
                              (show (nb067AlphaDummy251 f) ≠ (nb067AlphaDummy259 f) from
                                (by
                                  unfold nb067AlphaDummy259;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0275 f) 1))))
                              (TAlphaVar.there
                                (show (nb067AlphaDummy249) ≠ (nb067AlphaDummy255) from (by
                                    unfold nb067AlphaDummy255;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0274) 0)))) (show
                                  (nb067AlphaDummy251 f) ≠ (nb067AlphaDummy258 f) from (by
                                    unfold nb067AlphaDummy258;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0275 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb067AlphaDummy249) ≠ (nb067AlphaDummy253) from
                                    (by
                                      unfold nb067AlphaDummy253;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0272)
                                              0)))) (show
                                    (nb067AlphaDummy251 f) ≠ (nb067AlphaDummy254 f) from
                                    (by
                                      unfold nb067AlphaDummy254;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0273 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb067AlphaDummy257), (nb067AlphaDummy260 f)),
                                  ((nb067AlphaDummy256), (nb067AlphaDummy259 f)),
                                  ((nb067AlphaDummy255), (nb067AlphaDummy258 f)),
                                  ((nb067AlphaDummy253), (nb067AlphaDummy254 f)),
                                  ((nb067AlphaDummy249), (nb067AlphaDummy251 f)),
                                  ((nb067AlphaDummy250), (nb067AlphaDummy252 f)),
                                  ((nb067AlphaDummy242), (nb067AlphaDummy244 f)),
                                  ((nb067AlphaDummy241), (nb067AlphaDummy243 f)),
                                  ((nb067AlphaDummy247), (nb067AlphaDummy248 f)),
                                  ((nb067AlphaDummy245), (nb067AlphaDummy246 f)),
                                  ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                                  ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                                  ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                                  ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                                  ((nb067AlphaDummy000), f), ((nb067AlphaDummy003),
                                    (nb067AlphaDummy004 x y f)),
                                  ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                                  ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb067SplitAlpha0060 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb067AlphaDummy249) ≠ (nb067AlphaDummy253) from (by
                          unfold nb067AlphaDummy253;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0272) 0))))
                      (show (nb067AlphaDummy251 f) ≠ (nb067AlphaDummy254 f) from (by
                          unfold nb067AlphaDummy254;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0273 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb067AlphaDummy253), (nb067AlphaDummy254 f)),
                      ((nb067AlphaDummy249), (nb067AlphaDummy251 f)),
                      ((nb067AlphaDummy250), (nb067AlphaDummy252 f)),
                      ((nb067AlphaDummy242), (nb067AlphaDummy244 f)),
                      ((nb067AlphaDummy241), (nb067AlphaDummy243 f)),
                      ((nb067AlphaDummy247), (nb067AlphaDummy248 f)),
                      ((nb067AlphaDummy245), (nb067AlphaDummy246 f)),
                      ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                      ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                      ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                      ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                      ((nb067AlphaDummy000), f),
                      ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                      ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                      ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067AlphaDummy249) ≠ (nb067AlphaDummy253) from
                      (by
                        unfold nb067AlphaDummy253;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0272) 0))))
                    (show (nb067AlphaDummy251 f) ≠ (nb067AlphaDummy254 f) from (by
                        unfold nb067AlphaDummy254;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0273 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb067AlphaDummy249) ≠ (nb067AlphaDummy253) from (by
                          unfold nb067AlphaDummy253;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0272) 0))))
                      (show (nb067AlphaDummy251 f) ≠ (nb067AlphaDummy254 f) from (by
                          unfold nb067AlphaDummy254;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0273 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb067AlphaDummy253), (nb067AlphaDummy254 f)),
                      ((nb067AlphaDummy249), (nb067AlphaDummy251 f)),
                      ((nb067AlphaDummy250), (nb067AlphaDummy252 f)),
                      ((nb067AlphaDummy242), (nb067AlphaDummy244 f)),
                      ((nb067AlphaDummy241), (nb067AlphaDummy243 f)),
                      ((nb067AlphaDummy247), (nb067AlphaDummy248 f)),
                      ((nb067AlphaDummy245), (nb067AlphaDummy246 f)),
                      ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                      ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                      ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                      ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                      ((nb067AlphaDummy000), f),
                      ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                      ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                      ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0062`. -/
@[expose]
noncomputable def nb067SplitAlpha0062 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy257), (nb067AlphaDummy260 f)),
        ((nb067AlphaDummy256), (nb067AlphaDummy259 f)),
        ((nb067AlphaDummy255), (nb067AlphaDummy258 f)),
        ((nb067AlphaDummy253), (nb067AlphaDummy254 f)),
        ((nb067AlphaDummy249), (nb067AlphaDummy251 f)),
        ((nb067AlphaDummy250), (nb067AlphaDummy252 f)),
        ((nb067AlphaDummy275), (nb067AlphaDummy276 f)),
        ((nb067AlphaDummy273), (nb067AlphaDummy274 f)),
        ((nb067AlphaDummy242), (nb067AlphaDummy244 f)),
        ((nb067AlphaDummy241), (nb067AlphaDummy243 f)),
        ((nb067AlphaDummy271), (nb067AlphaDummy272 f)),
        ((nb067AlphaDummy245), (nb067AlphaDummy246 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb067AlphaDummy256)) (Class.cv (nb067AlphaDummy257)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb067AlphaDummy255))
            (synCun (Class.cv (nb067AlphaDummy256)) (Class.cv (nb067AlphaDummy257))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb067AlphaDummy259 f))
            (Class.cv (nb067AlphaDummy260 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy258 f))
            (synCun (Class.cv (nb067AlphaDummy259 f))
              (Class.cv (nb067AlphaDummy260 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy256) ≠ (nb067AlphaDummy263) from (by
                              unfold nb067AlphaDummy263;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0278) 0))))
                          (show (nb067AlphaDummy259 f) ≠ (nb067AlphaDummy264 f) from (by
                              unfold nb067AlphaDummy264;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0279 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy256) ≠ (nb067AlphaDummy261) from (by
                                unfold nb067AlphaDummy261;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0276) 0))))
                            (show (nb067AlphaDummy259 f) ≠ (nb067AlphaDummy262 f) from (by
                                unfold nb067AlphaDummy262;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0277 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy249))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy251 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy257) ≠ (nb067AlphaDummy263) from (by
                              unfold nb067AlphaDummy263;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0282) 0))))
                          (show (nb067AlphaDummy260 f) ≠ (nb067AlphaDummy264 f) from (by
                              unfold nb067AlphaDummy264;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0283 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy257) ≠ (nb067AlphaDummy261) from (by
                                unfold nb067AlphaDummy261;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0280) 0))))
                            (show (nb067AlphaDummy260 f) ≠ (nb067AlphaDummy262 f) from (by
                                unfold nb067AlphaDummy262;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0281 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy256) ≠ (nb067AlphaDummy263) from (by
                              unfold nb067AlphaDummy263;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0278) 0))))
                          (show (nb067AlphaDummy259 f) ≠ (nb067AlphaDummy264 f) from (by
                              unfold nb067AlphaDummy264;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0279 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy256) ≠ (nb067AlphaDummy261) from (by
                                unfold nb067AlphaDummy261;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0276) 0))))
                            (show (nb067AlphaDummy259 f) ≠ (nb067AlphaDummy262 f) from (by
                                unfold nb067AlphaDummy262;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0277 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy249))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy251 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy257) ≠ (nb067AlphaDummy263) from (by
                              unfold nb067AlphaDummy263;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0282) 0))))
                          (show (nb067AlphaDummy260 f) ≠ (nb067AlphaDummy264 f) from (by
                              unfold nb067AlphaDummy264;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0283 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy257) ≠ (nb067AlphaDummy261) from (by
                                unfold nb067AlphaDummy261;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0280) 0))))
                            (show (nb067AlphaDummy260 f) ≠ (nb067AlphaDummy262 f) from (by
                                unfold nb067AlphaDummy262;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0281 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb067AlphaDummy257), (nb067AlphaDummy260 f)),
          ((nb067AlphaDummy256), (nb067AlphaDummy259 f)),
          ((nb067AlphaDummy255), (nb067AlphaDummy258 f)),
          ((nb067AlphaDummy253), (nb067AlphaDummy254 f)),
          ((nb067AlphaDummy249), (nb067AlphaDummy251 f)),
          ((nb067AlphaDummy250), (nb067AlphaDummy252 f)),
          ((nb067AlphaDummy275), (nb067AlphaDummy276 f)),
          ((nb067AlphaDummy273), (nb067AlphaDummy274 f)),
          ((nb067AlphaDummy242), (nb067AlphaDummy244 f)),
          ((nb067AlphaDummy241), (nb067AlphaDummy243 f)),
          ((nb067AlphaDummy271), (nb067AlphaDummy272 f)),
          ((nb067AlphaDummy245), (nb067AlphaDummy246 f)),
          ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
          ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
          ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
          ((nb067AlphaDummy089), (nb067AlphaDummy090 f)), ((nb067AlphaDummy000), f),
          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy249))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067AlphaDummy251 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067AlphaDummy249))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067AlphaDummy251 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy256) ≠ (nb067AlphaDummy267) from (by
                                unfold nb067AlphaDummy267;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0286) 0))))
                            (show (nb067AlphaDummy259 f) ≠ (nb067AlphaDummy268 f) from (by
                                unfold nb067AlphaDummy268;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0287 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy256) ≠ (nb067AlphaDummy265) from (by
                                  unfold nb067AlphaDummy265;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0284) 0))))
                              (show (nb067AlphaDummy259 f) ≠ (nb067AlphaDummy266 f) from
                                (by
                                  unfold nb067AlphaDummy266;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0285 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy249))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy251 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy256) ≠ (nb067AlphaDummy267) from (by
                                unfold nb067AlphaDummy267;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0286) 0))))
                            (show (nb067AlphaDummy259 f) ≠ (nb067AlphaDummy268 f) from (by
                                unfold nb067AlphaDummy268;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0287 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy256) ≠ (nb067AlphaDummy265) from (by
                                  unfold nb067AlphaDummy265;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0284) 0))))
                              (show (nb067AlphaDummy259 f) ≠ (nb067AlphaDummy266 f) from
                                (by
                                  unfold nb067AlphaDummy266;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0285 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy249))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy251 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy257) ≠ (nb067AlphaDummy269) from (by
                                unfold nb067AlphaDummy269;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0290) 0))))
                            (show (nb067AlphaDummy260 f) ≠ (nb067AlphaDummy270 f) from (by
                                unfold nb067AlphaDummy270;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0291 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy257) ≠ (nb067AlphaDummy265) from (by
                                  unfold nb067AlphaDummy265;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0288) 0))))
                              (show (nb067AlphaDummy260 f) ≠ (nb067AlphaDummy266 f) from
                                (by
                                  unfold nb067AlphaDummy266;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0289 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy257) ≠ (nb067AlphaDummy269) from (by
                                unfold nb067AlphaDummy269;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0290) 0))))
                            (show (nb067AlphaDummy260 f) ≠ (nb067AlphaDummy270 f) from (by
                                unfold nb067AlphaDummy270;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0291 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy257) ≠ (nb067AlphaDummy265) from (by
                                  unfold nb067AlphaDummy265;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0288) 0))))
                              (show (nb067AlphaDummy260 f) ≠ (nb067AlphaDummy266 f) from
                                (by
                                  unfold nb067AlphaDummy266;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0289 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0063`. -/
@[expose]
noncomputable def nb067SplitAlpha0063 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy249), (nb067AlphaDummy251 f)),
        ((nb067AlphaDummy250), (nb067AlphaDummy252 f)),
        ((nb067AlphaDummy275), (nb067AlphaDummy276 f)),
        ((nb067AlphaDummy273), (nb067AlphaDummy274 f)),
        ((nb067AlphaDummy242), (nb067AlphaDummy244 f)),
        ((nb067AlphaDummy241), (nb067AlphaDummy243 f)),
        ((nb067AlphaDummy271), (nb067AlphaDummy272 f)),
        ((nb067AlphaDummy245), (nb067AlphaDummy246 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy249))
          (Class.cv (nb067AlphaDummy242))) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy250))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy249)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy249)) (synC1c))
              (Class.cv (nb067AlphaDummy249))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy251 f))
          (Class.cv (nb067AlphaDummy244 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy252 f))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy251 f)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy251 f)) (synC1c))
              (Class.cv (nb067AlphaDummy251 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067AlphaDummy242) ≠ (nb067AlphaDummy249) from (by
              unfold nb067AlphaDummy249;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0270) 0))))
          (show (nb067AlphaDummy244 f) ≠ (nb067AlphaDummy251 f) from (by
              unfold nb067AlphaDummy251;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0271 f) 0))))
          (TAlphaVar.there (show (nb067AlphaDummy242) ≠ (nb067AlphaDummy250) from (by
                unfold nb067AlphaDummy250;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0270) 1))))
            (show (nb067AlphaDummy244 f) ≠ (nb067AlphaDummy252 f) from (by
                unfold nb067AlphaDummy252;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0271 f) 1))))
            (TAlphaVar.there (show (nb067AlphaDummy242) ≠ (nb067AlphaDummy275) from (by
                  unfold nb067AlphaDummy275;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0300) 0))))
              (show (nb067AlphaDummy244 f) ≠ (nb067AlphaDummy276 f) from (by
                  unfold nb067AlphaDummy276;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0301 f) 0))))
              (TAlphaVar.there (show (nb067AlphaDummy242) ≠ (nb067AlphaDummy273) from (by
                    unfold nb067AlphaDummy273;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0298) 0))))
                (show (nb067AlphaDummy244 f) ≠ (nb067AlphaDummy274 f) from (by
                    unfold nb067AlphaDummy274;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0299 f) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy242))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb067AlphaDummy244 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb067AlphaDummy249) ≠ (nb067AlphaDummy256) from (by
                                  unfold nb067AlphaDummy256;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0274) 1))))
                              (show (nb067AlphaDummy251 f) ≠ (nb067AlphaDummy259 f) from
                                (by
                                  unfold nb067AlphaDummy259;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0275 f) 1))))
                              (TAlphaVar.there
                                (show (nb067AlphaDummy249) ≠ (nb067AlphaDummy255) from (by
                                    unfold nb067AlphaDummy255;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0274) 0)))) (show
                                  (nb067AlphaDummy251 f) ≠ (nb067AlphaDummy258 f) from (by
                                    unfold nb067AlphaDummy258;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0275 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb067AlphaDummy249) ≠ (nb067AlphaDummy253) from
                                    (by
                                      unfold nb067AlphaDummy253;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0272)
                                              0)))) (show
                                    (nb067AlphaDummy251 f) ≠ (nb067AlphaDummy254 f) from
                                    (by
                                      unfold nb067AlphaDummy254;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0273 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb067AlphaDummy257), (nb067AlphaDummy260 f)),
                                  ((nb067AlphaDummy256), (nb067AlphaDummy259 f)),
                                  ((nb067AlphaDummy255), (nb067AlphaDummy258 f)),
                                  ((nb067AlphaDummy253), (nb067AlphaDummy254 f)),
                                  ((nb067AlphaDummy249), (nb067AlphaDummy251 f)),
                                  ((nb067AlphaDummy250), (nb067AlphaDummy252 f)),
                                  ((nb067AlphaDummy275), (nb067AlphaDummy276 f)),
                                  ((nb067AlphaDummy273), (nb067AlphaDummy274 f)),
                                  ((nb067AlphaDummy242), (nb067AlphaDummy244 f)),
                                  ((nb067AlphaDummy241), (nb067AlphaDummy243 f)),
                                  ((nb067AlphaDummy271), (nb067AlphaDummy272 f)),
                                  ((nb067AlphaDummy245), (nb067AlphaDummy246 f)),
                                  ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                                  ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                                  ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                                  ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                                  ((nb067AlphaDummy000), f), ((nb067AlphaDummy003),
                                    (nb067AlphaDummy004 x y f)),
                                  ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                                  ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb067SplitAlpha0062 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb067AlphaDummy249) ≠ (nb067AlphaDummy253) from (by
                          unfold nb067AlphaDummy253;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0272) 0))))
                      (show (nb067AlphaDummy251 f) ≠ (nb067AlphaDummy254 f) from (by
                          unfold nb067AlphaDummy254;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0273 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb067AlphaDummy253), (nb067AlphaDummy254 f)),
                      ((nb067AlphaDummy249), (nb067AlphaDummy251 f)),
                      ((nb067AlphaDummy250), (nb067AlphaDummy252 f)),
                      ((nb067AlphaDummy275), (nb067AlphaDummy276 f)),
                      ((nb067AlphaDummy273), (nb067AlphaDummy274 f)),
                      ((nb067AlphaDummy242), (nb067AlphaDummy244 f)),
                      ((nb067AlphaDummy241), (nb067AlphaDummy243 f)),
                      ((nb067AlphaDummy271), (nb067AlphaDummy272 f)),
                      ((nb067AlphaDummy245), (nb067AlphaDummy246 f)),
                      ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                      ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                      ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                      ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                      ((nb067AlphaDummy000), f),
                      ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                      ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                      ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067AlphaDummy249) ≠ (nb067AlphaDummy253) from
                      (by
                        unfold nb067AlphaDummy253;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0272) 0))))
                    (show (nb067AlphaDummy251 f) ≠ (nb067AlphaDummy254 f) from (by
                        unfold nb067AlphaDummy254;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0273 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb067AlphaDummy249) ≠ (nb067AlphaDummy253) from (by
                          unfold nb067AlphaDummy253;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0272) 0))))
                      (show (nb067AlphaDummy251 f) ≠ (nb067AlphaDummy254 f) from (by
                          unfold nb067AlphaDummy254;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0273 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb067AlphaDummy253), (nb067AlphaDummy254 f)),
                      ((nb067AlphaDummy249), (nb067AlphaDummy251 f)),
                      ((nb067AlphaDummy250), (nb067AlphaDummy252 f)),
                      ((nb067AlphaDummy275), (nb067AlphaDummy276 f)),
                      ((nb067AlphaDummy273), (nb067AlphaDummy274 f)),
                      ((nb067AlphaDummy242), (nb067AlphaDummy244 f)),
                      ((nb067AlphaDummy241), (nb067AlphaDummy243 f)),
                      ((nb067AlphaDummy271), (nb067AlphaDummy272 f)),
                      ((nb067AlphaDummy245), (nb067AlphaDummy246 f)),
                      ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                      ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                      ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                      ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                      ((nb067AlphaDummy000), f),
                      ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                      ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                      ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0064`. -/
@[expose]
noncomputable def nb067SplitAlpha0064 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy271), (nb067AlphaDummy272 f)),
        ((nb067AlphaDummy245), (nb067AlphaDummy246 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy271))
          (Class.cab (nb067AlphaDummy241)
            (synWrex (nb067AlphaDummy242) (Class.cv (nb067AlphaDummy084))
              (Wff.classEq (Class.cv (nb067AlphaDummy241))
                (synCun (synCphi (Class.cv (nb067AlphaDummy242))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb067AlphaDummy271))
            (Class.cab (nb067AlphaDummy241)
              (synWrex (nb067AlphaDummy242) (Class.cv (nb067AlphaDummy084))
                (Wff.classEq (Class.cv (nb067AlphaDummy241))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy242)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy272 f))
          (Class.cab (nb067AlphaDummy243 f)
            (synWrex (nb067AlphaDummy244 f) (Class.cv (nb067AlphaDummy087 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy243 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy244 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb067AlphaDummy272 f))
            (Class.cab (nb067AlphaDummy243 f)
              (synWrex (nb067AlphaDummy244 f) (Class.cv (nb067AlphaDummy087 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy243 f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy244 f)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb067AlphaDummy084) ≠ (nb067AlphaDummy242) from
                    (by
                      unfold nb067AlphaDummy242;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0292) 1))))
                  (show (nb067AlphaDummy087 f) ≠ (nb067AlphaDummy244 f) from (by
                      unfold nb067AlphaDummy244;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0294 f) 1))))
                  (TAlphaVar.there (show (nb067AlphaDummy084) ≠ (nb067AlphaDummy241) from
                      (by
                        unfold nb067AlphaDummy241;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0292) 0))))
                    (show (nb067AlphaDummy087 f) ≠ (nb067AlphaDummy243 f) from (by
                        unfold nb067AlphaDummy243;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0294 f) 0)))) (TAlphaVar.there
                      (show (nb067AlphaDummy084) ≠ (nb067AlphaDummy271) from (by
                          unfold nb067AlphaDummy271;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0296) 0))))
                      (show (nb067AlphaDummy087 f) ≠ (nb067AlphaDummy272 f) from (by
                          unfold nb067AlphaDummy272;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0297 f) 0))))
                      (TAlphaVar.there
                        (show (nb067AlphaDummy084) ≠ (nb067AlphaDummy245) from (by
                            unfold nb067AlphaDummy245;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0293) 0))))
                        (show (nb067AlphaDummy087 f) ≠ (nb067AlphaDummy246 f) from (by
                            unfold nb067AlphaDummy246;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0295 f) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb067AlphaDummy000))).fv ∪
                              ((synCcnv (Class.cv (nb067AlphaDummy000)))).fv) (by decide))
                          (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb067AlphaDummy085))).fv ∪
                      ((Class.cv (nb067AlphaDummy084))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb067AlphaDummy088 f))).fv ∪
                      ((Class.cv (nb067AlphaDummy087 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067SplitAlpha0063 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067SplitAlpha0063 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb067AlphaDummy273), (nb067AlphaDummy274 f)),
                          ((nb067AlphaDummy242), (nb067AlphaDummy244 f)),
                          ((nb067AlphaDummy241), (nb067AlphaDummy243 f)),
                          ((nb067AlphaDummy271), (nb067AlphaDummy272 f)),
                          ((nb067AlphaDummy245), (nb067AlphaDummy246 f)),
                          ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                          ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                          ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                          ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                          ((nb067AlphaDummy000), f),
                          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067AlphaDummy084) ≠ (nb067AlphaDummy242) from
                      (by
                        unfold nb067AlphaDummy242;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0292) 1))))
                    (show (nb067AlphaDummy087 f) ≠ (nb067AlphaDummy244 f) from (by
                        unfold nb067AlphaDummy244;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0294 f) 1)))) (TAlphaVar.there
                      (show (nb067AlphaDummy084) ≠ (nb067AlphaDummy241) from (by
                          unfold nb067AlphaDummy241;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0292) 0))))
                      (show (nb067AlphaDummy087 f) ≠ (nb067AlphaDummy243 f) from (by
                          unfold nb067AlphaDummy243;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0294 f) 0))))
                      (TAlphaVar.there
                        (show (nb067AlphaDummy084) ≠ (nb067AlphaDummy271) from (by
                            unfold nb067AlphaDummy271;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0296) 0))))
                        (show (nb067AlphaDummy087 f) ≠ (nb067AlphaDummy272 f) from (by
                            unfold nb067AlphaDummy272;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0297 f) 0))))
                        (TAlphaVar.there
                          (show (nb067AlphaDummy084) ≠ (nb067AlphaDummy245) from (by
                              unfold nb067AlphaDummy245;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0293) 0))))
                          (show (nb067AlphaDummy087 f) ≠ (nb067AlphaDummy246 f) from (by
                              unfold nb067AlphaDummy246;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0295 f) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb067AlphaDummy000))).fv ∪
                                ((synCcnv (Class.cv (nb067AlphaDummy000)))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb067AlphaDummy085))).fv ∪
                        ((Class.cv (nb067AlphaDummy084))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb067AlphaDummy088 f))).fv ∪
                        ((Class.cv (nb067AlphaDummy087 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067SplitAlpha0063 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067SplitAlpha0063 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb067AlphaDummy273), (nb067AlphaDummy274 f)),
                            ((nb067AlphaDummy242), (nb067AlphaDummy244 f)),
                            ((nb067AlphaDummy241), (nb067AlphaDummy243 f)),
                            ((nb067AlphaDummy271), (nb067AlphaDummy272 f)),
                            ((nb067AlphaDummy245), (nb067AlphaDummy246 f)),
                            ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                            ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                            ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                            ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                            ((nb067AlphaDummy000), f),
                            ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                            ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                            ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0065`. -/
@[expose]
noncomputable def nb067SplitAlpha0065 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (synWbr (Class.cv (nb067AlphaDummy083))
          (synCcnv (Class.cv (nb067AlphaDummy000))) (Class.cv (nb067AlphaDummy085)))
        (Wff.neg (synWbr (Class.cv (nb067AlphaDummy085)) (Class.cv (nb067AlphaDummy000))
            (Class.cv (nb067AlphaDummy084)))))
      (Wff.imp (synWbr (Class.cv (nb067AlphaDummy086 f)) (synCcnv (Class.cv f))
          (Class.cv (nb067AlphaDummy088 f))) (Wff.neg
          (synWbr (Class.cv (nb067AlphaDummy088 f)) (Class.cv f)
            (Class.cv (nb067AlphaDummy087 f))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb067AlphaDummy083) ≠ (nb067AlphaDummy128) from
                                    (by
                                      unfold nb067AlphaDummy128;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0134)
                                              1)))) (show
                                    (nb067AlphaDummy086 f) ≠ (nb067AlphaDummy130 f) from
                                    (by
                                      unfold nb067AlphaDummy130;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0136 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb067AlphaDummy083) ≠ (nb067AlphaDummy127) from (by
                                        unfold nb067AlphaDummy127;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0134)
                                                0)))) (show (nb067AlphaDummy086 f) ≠
                                        (nb067AlphaDummy129 f) from (by
                                        unfold nb067AlphaDummy129;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0136 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb067AlphaDummy083) ≠ (nb067AlphaDummy133) from
                                        (by
                                          unfold nb067AlphaDummy133;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb067_support_mem_0138)
                                                  0)))) (show (nb067AlphaDummy086 f) ≠
        (nb067AlphaDummy134 f) from (by
                                          unfold nb067AlphaDummy134;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb067_support_mem_0139 f) 0))))
                                      (TAlphaVar.there (show (nb067AlphaDummy083) ≠
        (nb067AlphaDummy131) from (by
          unfold nb067AlphaDummy131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0135) 0)))) (show (nb067AlphaDummy086 f) ≠
        (nb067AlphaDummy132 f) from (by
          unfold nb067AlphaDummy132;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0137 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb067AlphaDummy000))).fv ∪ ((synCcnv
        (Class.cv (nb067AlphaDummy000)))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb067AlphaDummy000))).fv ∪ ((synCcnv (Class.cv
        (nb067AlphaDummy000)))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪
        ((synCcnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb067AlphaDummy083))).fv ∪
                                      ((Class.cv (nb067AlphaDummy085))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb067AlphaDummy086 f))).fv ∪
                                      ((Class.cv (nb067AlphaDummy088 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.all (nb067SplitAlpha0045 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb067AlphaDummy083) ≠ (nb067AlphaDummy128) from
                                    (by
                                      unfold nb067AlphaDummy128;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0134)
                                              1)))) (show
                                    (nb067AlphaDummy086 f) ≠ (nb067AlphaDummy130 f) from
                                    (by
                                      unfold nb067AlphaDummy130;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0136 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb067AlphaDummy083) ≠ (nb067AlphaDummy127) from (by
                                        unfold nb067AlphaDummy127;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0134)
                                                0)))) (show (nb067AlphaDummy086 f) ≠
                                        (nb067AlphaDummy129 f) from (by
                                        unfold nb067AlphaDummy129;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0136 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb067AlphaDummy083) ≠ (nb067AlphaDummy133) from
                                        (by
                                          unfold nb067AlphaDummy133;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb067_support_mem_0138)
                                                  0)))) (show (nb067AlphaDummy086 f) ≠
        (nb067AlphaDummy134 f) from (by
                                          unfold nb067AlphaDummy134;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb067_support_mem_0139 f) 0))))
                                      (TAlphaVar.there (show (nb067AlphaDummy083) ≠
        (nb067AlphaDummy131) from (by
          unfold nb067AlphaDummy131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0135) 0)))) (show (nb067AlphaDummy086 f) ≠
        (nb067AlphaDummy132 f) from (by
          unfold nb067AlphaDummy132;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0137 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb067AlphaDummy000))).fv ∪ ((synCcnv
        (Class.cv (nb067AlphaDummy000)))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb067AlphaDummy000))).fv ∪ ((synCcnv (Class.cv
        (nb067AlphaDummy000)))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪
        ((synCcnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb067AlphaDummy083))).fv ∪
                                      ((Class.cv (nb067AlphaDummy085))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb067AlphaDummy086 f))).fv ∪
                                      ((Class.cv (nb067AlphaDummy088 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.all (nb067SplitAlpha0045 x y f)))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb067SplitAlpha0048 x y f))))))))
      (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.neg (nb067SplitAlpha0059 x y f))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb067AlphaDummy085) ≠ (nb067AlphaDummy242) from (by
                                        unfold nb067AlphaDummy242;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0264)
                                                1)))) (show (nb067AlphaDummy088 f) ≠
                                        (nb067AlphaDummy244 f) from (by
                                        unfold nb067AlphaDummy244;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0266 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb067AlphaDummy085) ≠ (nb067AlphaDummy241) from
                                        (by
                                          unfold nb067AlphaDummy241;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb067_support_mem_0264)
                                                  0)))) (show (nb067AlphaDummy088 f) ≠
        (nb067AlphaDummy243 f) from (by
                                          unfold nb067AlphaDummy243;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb067_support_mem_0266 f) 0))))
                                      (TAlphaVar.there (show (nb067AlphaDummy085) ≠
        (nb067AlphaDummy247) from (by
          unfold nb067AlphaDummy247;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0268) 0)))) (show (nb067AlphaDummy088 f) ≠
        (nb067AlphaDummy248 f) from (by
          unfold nb067AlphaDummy248;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0269 f) 0)))) (TAlphaVar.there (show
        (nb067AlphaDummy085) ≠ (nb067AlphaDummy245) from (by
          unfold nb067AlphaDummy245;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0265) 0)))) (show (nb067AlphaDummy088 f) ≠
        (nb067AlphaDummy246 f) from (by
          unfold nb067AlphaDummy246;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0267 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb067AlphaDummy085))).fv ∪
                                        ((Class.cv (nb067AlphaDummy084))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb067AlphaDummy088 f))).fv ∪
                                        ((Class.cv (nb067AlphaDummy087 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.all (nb067SplitAlpha0061 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb067AlphaDummy085) ≠ (nb067AlphaDummy242) from (by
                                        unfold nb067AlphaDummy242;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0264)
                                                1)))) (show (nb067AlphaDummy088 f) ≠
                                        (nb067AlphaDummy244 f) from (by
                                        unfold nb067AlphaDummy244;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0266 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb067AlphaDummy085) ≠ (nb067AlphaDummy241) from
                                        (by
                                          unfold nb067AlphaDummy241;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb067_support_mem_0264)
                                                  0)))) (show (nb067AlphaDummy088 f) ≠
        (nb067AlphaDummy243 f) from (by
                                          unfold nb067AlphaDummy243;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb067_support_mem_0266 f) 0))))
                                      (TAlphaVar.there (show (nb067AlphaDummy085) ≠
        (nb067AlphaDummy247) from (by
          unfold nb067AlphaDummy247;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0268) 0)))) (show (nb067AlphaDummy088 f) ≠
        (nb067AlphaDummy248 f) from (by
          unfold nb067AlphaDummy248;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0269 f) 0)))) (TAlphaVar.there (show
        (nb067AlphaDummy085) ≠ (nb067AlphaDummy245) from (by
          unfold nb067AlphaDummy245;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0265) 0)))) (show (nb067AlphaDummy088 f) ≠
        (nb067AlphaDummy246 f) from (by
          unfold nb067AlphaDummy246;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0267 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb067AlphaDummy085))).fv ∪
                                        ((Class.cv (nb067AlphaDummy084))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb067AlphaDummy088 f))).fv ∪
                                        ((Class.cv (nb067AlphaDummy087 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.all (nb067SplitAlpha0061 x y f)))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb067SplitAlpha0064 x y f))))))))
        (TAlphaClass.cv (TAlphaVar.there
            (show (nb067AlphaDummy000) ≠ (nb067AlphaDummy085) from (by
                unfold nb067AlphaDummy085;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0256) 2))))
            (show f ≠ (nb067AlphaDummy088 f) from (by
                unfold nb067AlphaDummy088;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0258 f) 2))))
            (TAlphaVar.there (show (nb067AlphaDummy000) ≠ (nb067AlphaDummy084) from (by
                  unfold nb067AlphaDummy084;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0256) 1))))
              (show f ≠ (nb067AlphaDummy087 f) from (by
                  unfold nb067AlphaDummy087;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0258 f) 1))))
              (TAlphaVar.there (show (nb067AlphaDummy000) ≠ (nb067AlphaDummy083) from (by
                    unfold nb067AlphaDummy083;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0256) 0))))
                (show f ≠ (nb067AlphaDummy086 f) from (by
                    unfold nb067AlphaDummy086;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0258 f) 0))))
                (TAlphaVar.there (show (nb067AlphaDummy000) ≠ (nb067AlphaDummy089) from
                    (by
                      unfold nb067AlphaDummy089;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0257) 0))))
                  (show f ≠ (nb067AlphaDummy090 f) from (by
                      unfold nb067AlphaDummy090;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0259 f) 0))))
                  (TAlphaVar.here _ _ _)))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part028`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0066`. -/
@[expose]
noncomputable def nb067SplitAlpha0066 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy297), (nb067AlphaDummy300 f)),
        ((nb067AlphaDummy296), (nb067AlphaDummy299 f)),
        ((nb067AlphaDummy295), (nb067AlphaDummy298 f)),
        ((nb067AlphaDummy293), (nb067AlphaDummy294 f)),
        ((nb067AlphaDummy289), (nb067AlphaDummy291 f)),
        ((nb067AlphaDummy290), (nb067AlphaDummy292 f)),
        ((nb067AlphaDummy282), (nb067AlphaDummy284 f)),
        ((nb067AlphaDummy281), (nb067AlphaDummy283 f)),
        ((nb067AlphaDummy287), (nb067AlphaDummy288 f)),
        ((nb067AlphaDummy285), (nb067AlphaDummy286 f)),
        ((nb067AlphaDummy278), (nb067AlphaDummy280 f)),
        ((nb067AlphaDummy277), (nb067AlphaDummy279 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb067AlphaDummy296)) (Class.cv (nb067AlphaDummy297)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb067AlphaDummy295))
            (synCun (Class.cv (nb067AlphaDummy296)) (Class.cv (nb067AlphaDummy297))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb067AlphaDummy299 f))
            (Class.cv (nb067AlphaDummy300 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy298 f))
            (synCun (Class.cv (nb067AlphaDummy299 f))
              (Class.cv (nb067AlphaDummy300 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy296) ≠ (nb067AlphaDummy303) from (by
                              unfold nb067AlphaDummy303;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0316) 0))))
                          (show (nb067AlphaDummy299 f) ≠ (nb067AlphaDummy304 f) from (by
                              unfold nb067AlphaDummy304;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0317 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy296) ≠ (nb067AlphaDummy301) from (by
                                unfold nb067AlphaDummy301;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0314) 0))))
                            (show (nb067AlphaDummy299 f) ≠ (nb067AlphaDummy302 f) from (by
                                unfold nb067AlphaDummy302;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0315 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy289))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy291 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy297) ≠ (nb067AlphaDummy303) from (by
                              unfold nb067AlphaDummy303;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0320) 0))))
                          (show (nb067AlphaDummy300 f) ≠ (nb067AlphaDummy304 f) from (by
                              unfold nb067AlphaDummy304;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0321 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy297) ≠ (nb067AlphaDummy301) from (by
                                unfold nb067AlphaDummy301;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0318) 0))))
                            (show (nb067AlphaDummy300 f) ≠ (nb067AlphaDummy302 f) from (by
                                unfold nb067AlphaDummy302;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0319 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy296) ≠ (nb067AlphaDummy303) from (by
                              unfold nb067AlphaDummy303;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0316) 0))))
                          (show (nb067AlphaDummy299 f) ≠ (nb067AlphaDummy304 f) from (by
                              unfold nb067AlphaDummy304;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0317 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy296) ≠ (nb067AlphaDummy301) from (by
                                unfold nb067AlphaDummy301;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0314) 0))))
                            (show (nb067AlphaDummy299 f) ≠ (nb067AlphaDummy302 f) from (by
                                unfold nb067AlphaDummy302;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0315 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy289))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy291 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy297) ≠ (nb067AlphaDummy303) from (by
                              unfold nb067AlphaDummy303;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0320) 0))))
                          (show (nb067AlphaDummy300 f) ≠ (nb067AlphaDummy304 f) from (by
                              unfold nb067AlphaDummy304;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0321 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy297) ≠ (nb067AlphaDummy301) from (by
                                unfold nb067AlphaDummy301;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0318) 0))))
                            (show (nb067AlphaDummy300 f) ≠ (nb067AlphaDummy302 f) from (by
                                unfold nb067AlphaDummy302;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0319 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb067AlphaDummy297), (nb067AlphaDummy300 f)),
          ((nb067AlphaDummy296), (nb067AlphaDummy299 f)),
          ((nb067AlphaDummy295), (nb067AlphaDummy298 f)),
          ((nb067AlphaDummy293), (nb067AlphaDummy294 f)),
          ((nb067AlphaDummy289), (nb067AlphaDummy291 f)),
          ((nb067AlphaDummy290), (nb067AlphaDummy292 f)),
          ((nb067AlphaDummy282), (nb067AlphaDummy284 f)),
          ((nb067AlphaDummy281), (nb067AlphaDummy283 f)),
          ((nb067AlphaDummy287), (nb067AlphaDummy288 f)),
          ((nb067AlphaDummy285), (nb067AlphaDummy286 f)),
          ((nb067AlphaDummy278), (nb067AlphaDummy280 f)),
          ((nb067AlphaDummy277), (nb067AlphaDummy279 f)), ((nb067AlphaDummy000), f),
          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy289))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067AlphaDummy291 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067AlphaDummy289))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067AlphaDummy291 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy296) ≠ (nb067AlphaDummy307) from (by
                                unfold nb067AlphaDummy307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0324) 0))))
                            (show (nb067AlphaDummy299 f) ≠ (nb067AlphaDummy308 f) from (by
                                unfold nb067AlphaDummy308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0325 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy296) ≠ (nb067AlphaDummy305) from (by
                                  unfold nb067AlphaDummy305;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0322) 0))))
                              (show (nb067AlphaDummy299 f) ≠ (nb067AlphaDummy306 f) from
                                (by
                                  unfold nb067AlphaDummy306;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0323 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy289))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy291 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy296) ≠ (nb067AlphaDummy307) from (by
                                unfold nb067AlphaDummy307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0324) 0))))
                            (show (nb067AlphaDummy299 f) ≠ (nb067AlphaDummy308 f) from (by
                                unfold nb067AlphaDummy308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0325 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy296) ≠ (nb067AlphaDummy305) from (by
                                  unfold nb067AlphaDummy305;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0322) 0))))
                              (show (nb067AlphaDummy299 f) ≠ (nb067AlphaDummy306 f) from
                                (by
                                  unfold nb067AlphaDummy306;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0323 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy289))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy291 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy297) ≠ (nb067AlphaDummy309) from (by
                                unfold nb067AlphaDummy309;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0328) 0))))
                            (show (nb067AlphaDummy300 f) ≠ (nb067AlphaDummy310 f) from (by
                                unfold nb067AlphaDummy310;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0329 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy297) ≠ (nb067AlphaDummy305) from (by
                                  unfold nb067AlphaDummy305;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0326) 0))))
                              (show (nb067AlphaDummy300 f) ≠ (nb067AlphaDummy306 f) from
                                (by
                                  unfold nb067AlphaDummy306;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0327 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy297) ≠ (nb067AlphaDummy309) from (by
                                unfold nb067AlphaDummy309;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0328) 0))))
                            (show (nb067AlphaDummy300 f) ≠ (nb067AlphaDummy310 f) from (by
                                unfold nb067AlphaDummy310;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0329 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy297) ≠ (nb067AlphaDummy305) from (by
                                  unfold nb067AlphaDummy305;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0326) 0))))
                              (show (nb067AlphaDummy300 f) ≠ (nb067AlphaDummy306 f) from
                                (by
                                  unfold nb067AlphaDummy306;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0327 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0067`. -/
@[expose]
noncomputable def nb067SplitAlpha0067 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy282), (nb067AlphaDummy284 f)),
        ((nb067AlphaDummy281), (nb067AlphaDummy283 f)),
        ((nb067AlphaDummy287), (nb067AlphaDummy288 f)),
        ((nb067AlphaDummy285), (nb067AlphaDummy286 f)),
        ((nb067AlphaDummy278), (nb067AlphaDummy280 f)),
        ((nb067AlphaDummy277), (nb067AlphaDummy279 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.classEq (Class.cv (nb067AlphaDummy281))
        (synCphi (Class.cv (nb067AlphaDummy282))))
      (Wff.classEq (Class.cv (nb067AlphaDummy283 f))
        (synCphi (Class.cv (nb067AlphaDummy284 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb067AlphaDummy278))).fv ∪ ((Class.cv (nb067AlphaDummy277))).fv)
          (by decide)) (freshVar_injective (((Class.cv (nb067AlphaDummy280 f))).fv ∪
            ((Class.cv (nb067AlphaDummy279 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (show (nb067AlphaDummy282) ≠ (nb067AlphaDummy289) from (by
                    unfold nb067AlphaDummy289;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0308) 0))))
                (show (nb067AlphaDummy284 f) ≠ (nb067AlphaDummy291 f) from (by
                    unfold nb067AlphaDummy291;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0309 f) 0))))
                (TAlphaVar.there (show (nb067AlphaDummy282) ≠ (nb067AlphaDummy290) from
                    (by
                      unfold nb067AlphaDummy290;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0308) 1))))
                  (show (nb067AlphaDummy284 f) ≠ (nb067AlphaDummy292 f) from (by
                      unfold nb067AlphaDummy292;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0309 f) 1))))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb067AlphaDummy282))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb067AlphaDummy284 f))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb067AlphaDummy289) ≠ (nb067AlphaDummy296) from
                                    (by
                                      unfold nb067AlphaDummy296;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0312)
                                              1)))) (show
                                    (nb067AlphaDummy291 f) ≠ (nb067AlphaDummy299 f) from
                                    (by
                                      unfold nb067AlphaDummy299;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0313 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb067AlphaDummy289) ≠ (nb067AlphaDummy295) from (by
                                        unfold nb067AlphaDummy295;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0312)
                                                0)))) (show (nb067AlphaDummy291 f) ≠
                                        (nb067AlphaDummy298 f) from (by
                                        unfold nb067AlphaDummy298;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0313 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb067AlphaDummy289) ≠ (nb067AlphaDummy293) from
                                        (by
                                          unfold nb067AlphaDummy293;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb067_support_mem_0310)
                                                  0)))) (show (nb067AlphaDummy291 f) ≠
        (nb067AlphaDummy294 f) from (by
                                          unfold nb067AlphaDummy294;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb067_support_mem_0311 f) 0))))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.reflOfClosed
                                    [((nb067AlphaDummy297), (nb067AlphaDummy300 f)),
                                      ((nb067AlphaDummy296), (nb067AlphaDummy299 f)),
                                      ((nb067AlphaDummy295), (nb067AlphaDummy298 f)),
                                      ((nb067AlphaDummy293), (nb067AlphaDummy294 f)),
                                      ((nb067AlphaDummy289), (nb067AlphaDummy291 f)),
                                      ((nb067AlphaDummy290), (nb067AlphaDummy292 f)),
                                      ((nb067AlphaDummy282), (nb067AlphaDummy284 f)),
                                      ((nb067AlphaDummy281), (nb067AlphaDummy283 f)),
                                      ((nb067AlphaDummy287), (nb067AlphaDummy288 f)),
                                      ((nb067AlphaDummy285), (nb067AlphaDummy286 f)),
                                      ((nb067AlphaDummy278), (nb067AlphaDummy280 f)),
                                      ((nb067AlphaDummy277), (nb067AlphaDummy279 f)),
                                      ((nb067AlphaDummy000), f), ((nb067AlphaDummy003),
                                        (nb067AlphaDummy004 x y f)),
                                      ((nb067AlphaDummy002), y),
                                      ((nb067AlphaDummy001), x), ((nb067AlphaDummy005),
                                        (nb067AlphaDummy006 x y f))]
                                    (synC1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb067SplitAlpha0066 x y f))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (show (nb067AlphaDummy289) ≠ (nb067AlphaDummy293) from (by
                              unfold nb067AlphaDummy293;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0310) 0))))
                          (show (nb067AlphaDummy291 f) ≠ (nb067AlphaDummy294 f) from (by
                              unfold nb067AlphaDummy294;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0311 f) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb067AlphaDummy293), (nb067AlphaDummy294 f)),
                          ((nb067AlphaDummy289), (nb067AlphaDummy291 f)),
                          ((nb067AlphaDummy290), (nb067AlphaDummy292 f)),
                          ((nb067AlphaDummy282), (nb067AlphaDummy284 f)),
                          ((nb067AlphaDummy281), (nb067AlphaDummy283 f)),
                          ((nb067AlphaDummy287), (nb067AlphaDummy288 f)),
                          ((nb067AlphaDummy285), (nb067AlphaDummy286 f)),
                          ((nb067AlphaDummy278), (nb067AlphaDummy280 f)),
                          ((nb067AlphaDummy277), (nb067AlphaDummy279 f)),
                          ((nb067AlphaDummy000), f),
                          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb067AlphaDummy289) ≠ (nb067AlphaDummy293) from (by
                            unfold nb067AlphaDummy293;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0310) 0))))
                        (show (nb067AlphaDummy291 f) ≠ (nb067AlphaDummy294 f) from (by
                            unfold nb067AlphaDummy294;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0311 f) 0))))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (show (nb067AlphaDummy289) ≠ (nb067AlphaDummy293) from (by
                              unfold nb067AlphaDummy293;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0310) 0))))
                          (show (nb067AlphaDummy291 f) ≠ (nb067AlphaDummy294 f) from (by
                              unfold nb067AlphaDummy294;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0311 f) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb067AlphaDummy293), (nb067AlphaDummy294 f)),
                          ((nb067AlphaDummy289), (nb067AlphaDummy291 f)),
                          ((nb067AlphaDummy290), (nb067AlphaDummy292 f)),
                          ((nb067AlphaDummy282), (nb067AlphaDummy284 f)),
                          ((nb067AlphaDummy281), (nb067AlphaDummy283 f)),
                          ((nb067AlphaDummy287), (nb067AlphaDummy288 f)),
                          ((nb067AlphaDummy285), (nb067AlphaDummy286 f)),
                          ((nb067AlphaDummy278), (nb067AlphaDummy280 f)),
                          ((nb067AlphaDummy277), (nb067AlphaDummy279 f)),
                          ((nb067AlphaDummy000), f),
                          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0068`. -/
@[expose]
noncomputable def nb067SplitAlpha0068 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy297), (nb067AlphaDummy300 f)),
        ((nb067AlphaDummy296), (nb067AlphaDummy299 f)),
        ((nb067AlphaDummy295), (nb067AlphaDummy298 f)),
        ((nb067AlphaDummy293), (nb067AlphaDummy294 f)),
        ((nb067AlphaDummy289), (nb067AlphaDummy291 f)),
        ((nb067AlphaDummy290), (nb067AlphaDummy292 f)),
        ((nb067AlphaDummy315), (nb067AlphaDummy316 f)),
        ((nb067AlphaDummy313), (nb067AlphaDummy314 f)),
        ((nb067AlphaDummy282), (nb067AlphaDummy284 f)),
        ((nb067AlphaDummy281), (nb067AlphaDummy283 f)),
        ((nb067AlphaDummy311), (nb067AlphaDummy312 f)),
        ((nb067AlphaDummy285), (nb067AlphaDummy286 f)),
        ((nb067AlphaDummy278), (nb067AlphaDummy280 f)),
        ((nb067AlphaDummy277), (nb067AlphaDummy279 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb067AlphaDummy296)) (Class.cv (nb067AlphaDummy297)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb067AlphaDummy295))
            (synCun (Class.cv (nb067AlphaDummy296)) (Class.cv (nb067AlphaDummy297))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb067AlphaDummy299 f))
            (Class.cv (nb067AlphaDummy300 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy298 f))
            (synCun (Class.cv (nb067AlphaDummy299 f))
              (Class.cv (nb067AlphaDummy300 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy296) ≠ (nb067AlphaDummy303) from (by
                              unfold nb067AlphaDummy303;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0316) 0))))
                          (show (nb067AlphaDummy299 f) ≠ (nb067AlphaDummy304 f) from (by
                              unfold nb067AlphaDummy304;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0317 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy296) ≠ (nb067AlphaDummy301) from (by
                                unfold nb067AlphaDummy301;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0314) 0))))
                            (show (nb067AlphaDummy299 f) ≠ (nb067AlphaDummy302 f) from (by
                                unfold nb067AlphaDummy302;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0315 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy289))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy291 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy297) ≠ (nb067AlphaDummy303) from (by
                              unfold nb067AlphaDummy303;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0320) 0))))
                          (show (nb067AlphaDummy300 f) ≠ (nb067AlphaDummy304 f) from (by
                              unfold nb067AlphaDummy304;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0321 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy297) ≠ (nb067AlphaDummy301) from (by
                                unfold nb067AlphaDummy301;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0318) 0))))
                            (show (nb067AlphaDummy300 f) ≠ (nb067AlphaDummy302 f) from (by
                                unfold nb067AlphaDummy302;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0319 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy296) ≠ (nb067AlphaDummy303) from (by
                              unfold nb067AlphaDummy303;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0316) 0))))
                          (show (nb067AlphaDummy299 f) ≠ (nb067AlphaDummy304 f) from (by
                              unfold nb067AlphaDummy304;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0317 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy296) ≠ (nb067AlphaDummy301) from (by
                                unfold nb067AlphaDummy301;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0314) 0))))
                            (show (nb067AlphaDummy299 f) ≠ (nb067AlphaDummy302 f) from (by
                                unfold nb067AlphaDummy302;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0315 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy289))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy291 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy297) ≠ (nb067AlphaDummy303) from (by
                              unfold nb067AlphaDummy303;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0320) 0))))
                          (show (nb067AlphaDummy300 f) ≠ (nb067AlphaDummy304 f) from (by
                              unfold nb067AlphaDummy304;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0321 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy297) ≠ (nb067AlphaDummy301) from (by
                                unfold nb067AlphaDummy301;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0318) 0))))
                            (show (nb067AlphaDummy300 f) ≠ (nb067AlphaDummy302 f) from (by
                                unfold nb067AlphaDummy302;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0319 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb067AlphaDummy297), (nb067AlphaDummy300 f)),
          ((nb067AlphaDummy296), (nb067AlphaDummy299 f)),
          ((nb067AlphaDummy295), (nb067AlphaDummy298 f)),
          ((nb067AlphaDummy293), (nb067AlphaDummy294 f)),
          ((nb067AlphaDummy289), (nb067AlphaDummy291 f)),
          ((nb067AlphaDummy290), (nb067AlphaDummy292 f)),
          ((nb067AlphaDummy315), (nb067AlphaDummy316 f)),
          ((nb067AlphaDummy313), (nb067AlphaDummy314 f)),
          ((nb067AlphaDummy282), (nb067AlphaDummy284 f)),
          ((nb067AlphaDummy281), (nb067AlphaDummy283 f)),
          ((nb067AlphaDummy311), (nb067AlphaDummy312 f)),
          ((nb067AlphaDummy285), (nb067AlphaDummy286 f)),
          ((nb067AlphaDummy278), (nb067AlphaDummy280 f)),
          ((nb067AlphaDummy277), (nb067AlphaDummy279 f)), ((nb067AlphaDummy000), f),
          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy289))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067AlphaDummy291 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067AlphaDummy289))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067AlphaDummy291 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy296) ≠ (nb067AlphaDummy307) from (by
                                unfold nb067AlphaDummy307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0324) 0))))
                            (show (nb067AlphaDummy299 f) ≠ (nb067AlphaDummy308 f) from (by
                                unfold nb067AlphaDummy308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0325 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy296) ≠ (nb067AlphaDummy305) from (by
                                  unfold nb067AlphaDummy305;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0322) 0))))
                              (show (nb067AlphaDummy299 f) ≠ (nb067AlphaDummy306 f) from
                                (by
                                  unfold nb067AlphaDummy306;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0323 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy289))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy291 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy296) ≠ (nb067AlphaDummy307) from (by
                                unfold nb067AlphaDummy307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0324) 0))))
                            (show (nb067AlphaDummy299 f) ≠ (nb067AlphaDummy308 f) from (by
                                unfold nb067AlphaDummy308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0325 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy296) ≠ (nb067AlphaDummy305) from (by
                                  unfold nb067AlphaDummy305;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0322) 0))))
                              (show (nb067AlphaDummy299 f) ≠ (nb067AlphaDummy306 f) from
                                (by
                                  unfold nb067AlphaDummy306;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0323 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy289))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy291 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy297) ≠ (nb067AlphaDummy309) from (by
                                unfold nb067AlphaDummy309;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0328) 0))))
                            (show (nb067AlphaDummy300 f) ≠ (nb067AlphaDummy310 f) from (by
                                unfold nb067AlphaDummy310;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0329 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy297) ≠ (nb067AlphaDummy305) from (by
                                  unfold nb067AlphaDummy305;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0326) 0))))
                              (show (nb067AlphaDummy300 f) ≠ (nb067AlphaDummy306 f) from
                                (by
                                  unfold nb067AlphaDummy306;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0327 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy297) ≠ (nb067AlphaDummy309) from (by
                                unfold nb067AlphaDummy309;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0328) 0))))
                            (show (nb067AlphaDummy300 f) ≠ (nb067AlphaDummy310 f) from (by
                                unfold nb067AlphaDummy310;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0329 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy297) ≠ (nb067AlphaDummy305) from (by
                                  unfold nb067AlphaDummy305;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0326) 0))))
                              (show (nb067AlphaDummy300 f) ≠ (nb067AlphaDummy306 f) from
                                (by
                                  unfold nb067AlphaDummy306;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0327 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part029`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0069`. -/
@[expose]
noncomputable def nb067SplitAlpha0069 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy289), (nb067AlphaDummy291 f)),
        ((nb067AlphaDummy290), (nb067AlphaDummy292 f)),
        ((nb067AlphaDummy315), (nb067AlphaDummy316 f)),
        ((nb067AlphaDummy313), (nb067AlphaDummy314 f)),
        ((nb067AlphaDummy282), (nb067AlphaDummy284 f)),
        ((nb067AlphaDummy281), (nb067AlphaDummy283 f)),
        ((nb067AlphaDummy311), (nb067AlphaDummy312 f)),
        ((nb067AlphaDummy285), (nb067AlphaDummy286 f)),
        ((nb067AlphaDummy278), (nb067AlphaDummy280 f)),
        ((nb067AlphaDummy277), (nb067AlphaDummy279 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy289))
          (Class.cv (nb067AlphaDummy282))) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy290))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy289)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy289)) (synC1c))
              (Class.cv (nb067AlphaDummy289))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy291 f))
          (Class.cv (nb067AlphaDummy284 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy292 f))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy291 f)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy291 f)) (synC1c))
              (Class.cv (nb067AlphaDummy291 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067AlphaDummy282) ≠ (nb067AlphaDummy289) from (by
              unfold nb067AlphaDummy289;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0308) 0))))
          (show (nb067AlphaDummy284 f) ≠ (nb067AlphaDummy291 f) from (by
              unfold nb067AlphaDummy291;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0309 f) 0))))
          (TAlphaVar.there (show (nb067AlphaDummy282) ≠ (nb067AlphaDummy290) from (by
                unfold nb067AlphaDummy290;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0308) 1))))
            (show (nb067AlphaDummy284 f) ≠ (nb067AlphaDummy292 f) from (by
                unfold nb067AlphaDummy292;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0309 f) 1))))
            (TAlphaVar.there (show (nb067AlphaDummy282) ≠ (nb067AlphaDummy315) from (by
                  unfold nb067AlphaDummy315;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0338) 0))))
              (show (nb067AlphaDummy284 f) ≠ (nb067AlphaDummy316 f) from (by
                  unfold nb067AlphaDummy316;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0339 f) 0))))
              (TAlphaVar.there (show (nb067AlphaDummy282) ≠ (nb067AlphaDummy313) from (by
                    unfold nb067AlphaDummy313;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0336) 0))))
                (show (nb067AlphaDummy284 f) ≠ (nb067AlphaDummy314 f) from (by
                    unfold nb067AlphaDummy314;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0337 f) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy282))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb067AlphaDummy284 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb067AlphaDummy289) ≠ (nb067AlphaDummy296) from (by
                                  unfold nb067AlphaDummy296;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0312) 1))))
                              (show (nb067AlphaDummy291 f) ≠ (nb067AlphaDummy299 f) from
                                (by
                                  unfold nb067AlphaDummy299;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0313 f) 1))))
                              (TAlphaVar.there
                                (show (nb067AlphaDummy289) ≠ (nb067AlphaDummy295) from (by
                                    unfold nb067AlphaDummy295;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0312) 0)))) (show
                                  (nb067AlphaDummy291 f) ≠ (nb067AlphaDummy298 f) from (by
                                    unfold nb067AlphaDummy298;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0313 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb067AlphaDummy289) ≠ (nb067AlphaDummy293) from
                                    (by
                                      unfold nb067AlphaDummy293;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0310)
                                              0)))) (show
                                    (nb067AlphaDummy291 f) ≠ (nb067AlphaDummy294 f) from
                                    (by
                                      unfold nb067AlphaDummy294;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0311 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb067AlphaDummy297), (nb067AlphaDummy300 f)),
                                  ((nb067AlphaDummy296), (nb067AlphaDummy299 f)),
                                  ((nb067AlphaDummy295), (nb067AlphaDummy298 f)),
                                  ((nb067AlphaDummy293), (nb067AlphaDummy294 f)),
                                  ((nb067AlphaDummy289), (nb067AlphaDummy291 f)),
                                  ((nb067AlphaDummy290), (nb067AlphaDummy292 f)),
                                  ((nb067AlphaDummy315), (nb067AlphaDummy316 f)),
                                  ((nb067AlphaDummy313), (nb067AlphaDummy314 f)),
                                  ((nb067AlphaDummy282), (nb067AlphaDummy284 f)),
                                  ((nb067AlphaDummy281), (nb067AlphaDummy283 f)),
                                  ((nb067AlphaDummy311), (nb067AlphaDummy312 f)),
                                  ((nb067AlphaDummy285), (nb067AlphaDummy286 f)),
                                  ((nb067AlphaDummy278), (nb067AlphaDummy280 f)),
                                  ((nb067AlphaDummy277), (nb067AlphaDummy279 f)),
                                  ((nb067AlphaDummy000), f), ((nb067AlphaDummy003),
                                    (nb067AlphaDummy004 x y f)),
                                  ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                                  ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb067SplitAlpha0068 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb067AlphaDummy289) ≠ (nb067AlphaDummy293) from (by
                          unfold nb067AlphaDummy293;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0310) 0))))
                      (show (nb067AlphaDummy291 f) ≠ (nb067AlphaDummy294 f) from (by
                          unfold nb067AlphaDummy294;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0311 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb067AlphaDummy293), (nb067AlphaDummy294 f)),
                      ((nb067AlphaDummy289), (nb067AlphaDummy291 f)),
                      ((nb067AlphaDummy290), (nb067AlphaDummy292 f)),
                      ((nb067AlphaDummy315), (nb067AlphaDummy316 f)),
                      ((nb067AlphaDummy313), (nb067AlphaDummy314 f)),
                      ((nb067AlphaDummy282), (nb067AlphaDummy284 f)),
                      ((nb067AlphaDummy281), (nb067AlphaDummy283 f)),
                      ((nb067AlphaDummy311), (nb067AlphaDummy312 f)),
                      ((nb067AlphaDummy285), (nb067AlphaDummy286 f)),
                      ((nb067AlphaDummy278), (nb067AlphaDummy280 f)),
                      ((nb067AlphaDummy277), (nb067AlphaDummy279 f)),
                      ((nb067AlphaDummy000), f),
                      ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                      ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                      ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067AlphaDummy289) ≠ (nb067AlphaDummy293) from
                      (by
                        unfold nb067AlphaDummy293;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0310) 0))))
                    (show (nb067AlphaDummy291 f) ≠ (nb067AlphaDummy294 f) from (by
                        unfold nb067AlphaDummy294;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0311 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb067AlphaDummy289) ≠ (nb067AlphaDummy293) from (by
                          unfold nb067AlphaDummy293;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0310) 0))))
                      (show (nb067AlphaDummy291 f) ≠ (nb067AlphaDummy294 f) from (by
                          unfold nb067AlphaDummy294;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0311 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb067AlphaDummy293), (nb067AlphaDummy294 f)),
                      ((nb067AlphaDummy289), (nb067AlphaDummy291 f)),
                      ((nb067AlphaDummy290), (nb067AlphaDummy292 f)),
                      ((nb067AlphaDummy315), (nb067AlphaDummy316 f)),
                      ((nb067AlphaDummy313), (nb067AlphaDummy314 f)),
                      ((nb067AlphaDummy282), (nb067AlphaDummy284 f)),
                      ((nb067AlphaDummy281), (nb067AlphaDummy283 f)),
                      ((nb067AlphaDummy311), (nb067AlphaDummy312 f)),
                      ((nb067AlphaDummy285), (nb067AlphaDummy286 f)),
                      ((nb067AlphaDummy278), (nb067AlphaDummy280 f)),
                      ((nb067AlphaDummy277), (nb067AlphaDummy279 f)),
                      ((nb067AlphaDummy000), f),
                      ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                      ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                      ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0070`. -/
@[expose]
noncomputable def nb067SplitAlpha0070 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy311), (nb067AlphaDummy312 f)),
        ((nb067AlphaDummy285), (nb067AlphaDummy286 f)),
        ((nb067AlphaDummy278), (nb067AlphaDummy280 f)),
        ((nb067AlphaDummy277), (nb067AlphaDummy279 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy311))
          (Class.cab (nb067AlphaDummy281)
            (synWrex (nb067AlphaDummy282) (Class.cv (nb067AlphaDummy277))
              (Wff.classEq (Class.cv (nb067AlphaDummy281))
                (synCun (synCphi (Class.cv (nb067AlphaDummy282))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb067AlphaDummy311))
            (Class.cab (nb067AlphaDummy281)
              (synWrex (nb067AlphaDummy282) (Class.cv (nb067AlphaDummy277))
                (Wff.classEq (Class.cv (nb067AlphaDummy281))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy282)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy312 f))
          (Class.cab (nb067AlphaDummy283 f)
            (synWrex (nb067AlphaDummy284 f) (Class.cv (nb067AlphaDummy279 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy283 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy284 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb067AlphaDummy312 f))
            (Class.cab (nb067AlphaDummy283 f)
              (synWrex (nb067AlphaDummy284 f) (Class.cv (nb067AlphaDummy279 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy283 f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy284 f)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb067AlphaDummy277) ≠ (nb067AlphaDummy282) from
                    (by
                      unfold nb067AlphaDummy282;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0330) 1))))
                  (show (nb067AlphaDummy279 f) ≠ (nb067AlphaDummy284 f) from (by
                      unfold nb067AlphaDummy284;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0332 f) 1))))
                  (TAlphaVar.there (show (nb067AlphaDummy277) ≠ (nb067AlphaDummy281) from
                      (by
                        unfold nb067AlphaDummy281;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0330) 0))))
                    (show (nb067AlphaDummy279 f) ≠ (nb067AlphaDummy283 f) from (by
                        unfold nb067AlphaDummy283;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0332 f) 0)))) (TAlphaVar.there
                      (show (nb067AlphaDummy277) ≠ (nb067AlphaDummy311) from (by
                          unfold nb067AlphaDummy311;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0334) 0))))
                      (show (nb067AlphaDummy279 f) ≠ (nb067AlphaDummy312 f) from (by
                          unfold nb067AlphaDummy312;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0335 f) 0))))
                      (TAlphaVar.there
                        (show (nb067AlphaDummy277) ≠ (nb067AlphaDummy285) from (by
                            unfold nb067AlphaDummy285;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0331) 0))))
                        (show (nb067AlphaDummy279 f) ≠ (nb067AlphaDummy286 f) from (by
                            unfold nb067AlphaDummy286;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0333 f) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((synCcnv (Class.cv (nb067AlphaDummy000)))).fv ∪
                              ((synCvv)).fv) (by decide)) (freshVar_injective
                            (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb067AlphaDummy278))).fv ∪
                      ((Class.cv (nb067AlphaDummy277))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb067AlphaDummy280 f))).fv ∪
                      ((Class.cv (nb067AlphaDummy279 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067SplitAlpha0069 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067SplitAlpha0069 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb067AlphaDummy313), (nb067AlphaDummy314 f)),
                          ((nb067AlphaDummy282), (nb067AlphaDummy284 f)),
                          ((nb067AlphaDummy281), (nb067AlphaDummy283 f)),
                          ((nb067AlphaDummy311), (nb067AlphaDummy312 f)),
                          ((nb067AlphaDummy285), (nb067AlphaDummy286 f)),
                          ((nb067AlphaDummy278), (nb067AlphaDummy280 f)),
                          ((nb067AlphaDummy277), (nb067AlphaDummy279 f)),
                          ((nb067AlphaDummy000), f),
                          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067AlphaDummy277) ≠ (nb067AlphaDummy282) from
                      (by
                        unfold nb067AlphaDummy282;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0330) 1))))
                    (show (nb067AlphaDummy279 f) ≠ (nb067AlphaDummy284 f) from (by
                        unfold nb067AlphaDummy284;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0332 f) 1)))) (TAlphaVar.there
                      (show (nb067AlphaDummy277) ≠ (nb067AlphaDummy281) from (by
                          unfold nb067AlphaDummy281;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0330) 0))))
                      (show (nb067AlphaDummy279 f) ≠ (nb067AlphaDummy283 f) from (by
                          unfold nb067AlphaDummy283;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0332 f) 0))))
                      (TAlphaVar.there
                        (show (nb067AlphaDummy277) ≠ (nb067AlphaDummy311) from (by
                            unfold nb067AlphaDummy311;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0334) 0))))
                        (show (nb067AlphaDummy279 f) ≠ (nb067AlphaDummy312 f) from (by
                            unfold nb067AlphaDummy312;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0335 f) 0))))
                        (TAlphaVar.there
                          (show (nb067AlphaDummy277) ≠ (nb067AlphaDummy285) from (by
                              unfold nb067AlphaDummy285;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0331) 0))))
                          (show (nb067AlphaDummy279 f) ≠ (nb067AlphaDummy286 f) from (by
                              unfold nb067AlphaDummy286;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0333 f) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((synCcnv (Class.cv (nb067AlphaDummy000)))).fv ∪
                                ((synCvv)).fv) (by decide)) (freshVar_injective
                              (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb067AlphaDummy278))).fv ∪
                        ((Class.cv (nb067AlphaDummy277))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb067AlphaDummy280 f))).fv ∪
                        ((Class.cv (nb067AlphaDummy279 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067SplitAlpha0069 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067SplitAlpha0069 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb067AlphaDummy313), (nb067AlphaDummy314 f)),
                            ((nb067AlphaDummy282), (nb067AlphaDummy284 f)),
                            ((nb067AlphaDummy281), (nb067AlphaDummy283 f)),
                            ((nb067AlphaDummy311), (nb067AlphaDummy312 f)),
                            ((nb067AlphaDummy285), (nb067AlphaDummy286 f)),
                            ((nb067AlphaDummy278), (nb067AlphaDummy280 f)),
                            ((nb067AlphaDummy277), (nb067AlphaDummy279 f)),
                            ((nb067AlphaDummy000), f),
                            ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                            ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                            ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0071`. -/
@[expose]
noncomputable def nb067SplitAlpha0071 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy185), (nb067AlphaDummy188 f)),
        ((nb067AlphaDummy184), (nb067AlphaDummy187 f)),
        ((nb067AlphaDummy183), (nb067AlphaDummy186 f)),
        ((nb067AlphaDummy181), (nb067AlphaDummy182 f)),
        ((nb067AlphaDummy177), (nb067AlphaDummy179 f)),
        ((nb067AlphaDummy178), (nb067AlphaDummy180 f)),
        ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
        ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
        ((nb067AlphaDummy175), (nb067AlphaDummy176 f)),
        ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
        ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
        ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
        ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
        ((nb067AlphaDummy278), (nb067AlphaDummy280 f)),
        ((nb067AlphaDummy277), (nb067AlphaDummy279 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb067AlphaDummy184)) (Class.cv (nb067AlphaDummy185)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb067AlphaDummy183))
            (synCun (Class.cv (nb067AlphaDummy184)) (Class.cv (nb067AlphaDummy185))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb067AlphaDummy187 f))
            (Class.cv (nb067AlphaDummy188 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy186 f))
            (synCun (Class.cv (nb067AlphaDummy187 f))
              (Class.cv (nb067AlphaDummy188 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy184) ≠ (nb067AlphaDummy191) from (by
                              unfold nb067AlphaDummy191;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0190) 0))))
                          (show (nb067AlphaDummy187 f) ≠ (nb067AlphaDummy192 f) from (by
                              unfold nb067AlphaDummy192;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0191 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy184) ≠ (nb067AlphaDummy189) from (by
                                unfold nb067AlphaDummy189;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0188) 0))))
                            (show (nb067AlphaDummy187 f) ≠ (nb067AlphaDummy190 f) from (by
                                unfold nb067AlphaDummy190;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0189 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy185) ≠ (nb067AlphaDummy191) from (by
                              unfold nb067AlphaDummy191;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0194) 0))))
                          (show (nb067AlphaDummy188 f) ≠ (nb067AlphaDummy192 f) from (by
                              unfold nb067AlphaDummy192;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0195 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy185) ≠ (nb067AlphaDummy189) from (by
                                unfold nb067AlphaDummy189;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0192) 0))))
                            (show (nb067AlphaDummy188 f) ≠ (nb067AlphaDummy190 f) from (by
                                unfold nb067AlphaDummy190;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0193 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy184) ≠ (nb067AlphaDummy191) from (by
                              unfold nb067AlphaDummy191;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0190) 0))))
                          (show (nb067AlphaDummy187 f) ≠ (nb067AlphaDummy192 f) from (by
                              unfold nb067AlphaDummy192;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0191 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy184) ≠ (nb067AlphaDummy189) from (by
                                unfold nb067AlphaDummy189;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0188) 0))))
                            (show (nb067AlphaDummy187 f) ≠ (nb067AlphaDummy190 f) from (by
                                unfold nb067AlphaDummy190;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0189 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy185) ≠ (nb067AlphaDummy191) from (by
                              unfold nb067AlphaDummy191;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0194) 0))))
                          (show (nb067AlphaDummy188 f) ≠ (nb067AlphaDummy192 f) from (by
                              unfold nb067AlphaDummy192;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0195 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy185) ≠ (nb067AlphaDummy189) from (by
                                unfold nb067AlphaDummy189;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0192) 0))))
                            (show (nb067AlphaDummy188 f) ≠ (nb067AlphaDummy190 f) from (by
                                unfold nb067AlphaDummy190;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0193 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb067AlphaDummy185), (nb067AlphaDummy188 f)),
          ((nb067AlphaDummy184), (nb067AlphaDummy187 f)),
          ((nb067AlphaDummy183), (nb067AlphaDummy186 f)),
          ((nb067AlphaDummy181), (nb067AlphaDummy182 f)),
          ((nb067AlphaDummy177), (nb067AlphaDummy179 f)),
          ((nb067AlphaDummy178), (nb067AlphaDummy180 f)),
          ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
          ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
          ((nb067AlphaDummy175), (nb067AlphaDummy176 f)),
          ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
          ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
          ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
          ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
          ((nb067AlphaDummy278), (nb067AlphaDummy280 f)),
          ((nb067AlphaDummy277), (nb067AlphaDummy279 f)), ((nb067AlphaDummy000), f),
          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy184) ≠ (nb067AlphaDummy195) from (by
                                unfold nb067AlphaDummy195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0198) 0))))
                            (show (nb067AlphaDummy187 f) ≠ (nb067AlphaDummy196 f) from (by
                                unfold nb067AlphaDummy196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0199 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy184) ≠ (nb067AlphaDummy193) from (by
                                  unfold nb067AlphaDummy193;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0196) 0))))
                              (show (nb067AlphaDummy187 f) ≠ (nb067AlphaDummy194 f) from
                                (by
                                  unfold nb067AlphaDummy194;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0197 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy184) ≠ (nb067AlphaDummy195) from (by
                                unfold nb067AlphaDummy195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0198) 0))))
                            (show (nb067AlphaDummy187 f) ≠ (nb067AlphaDummy196 f) from (by
                                unfold nb067AlphaDummy196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0199 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy184) ≠ (nb067AlphaDummy193) from (by
                                  unfold nb067AlphaDummy193;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0196) 0))))
                              (show (nb067AlphaDummy187 f) ≠ (nb067AlphaDummy194 f) from
                                (by
                                  unfold nb067AlphaDummy194;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0197 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy185) ≠ (nb067AlphaDummy197) from (by
                                unfold nb067AlphaDummy197;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0202) 0))))
                            (show (nb067AlphaDummy188 f) ≠ (nb067AlphaDummy198 f) from (by
                                unfold nb067AlphaDummy198;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0203 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy185) ≠ (nb067AlphaDummy193) from (by
                                  unfold nb067AlphaDummy193;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0200) 0))))
                              (show (nb067AlphaDummy188 f) ≠ (nb067AlphaDummy194 f) from
                                (by
                                  unfold nb067AlphaDummy194;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0201 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy185) ≠ (nb067AlphaDummy197) from (by
                                unfold nb067AlphaDummy197;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0202) 0))))
                            (show (nb067AlphaDummy188 f) ≠ (nb067AlphaDummy198 f) from (by
                                unfold nb067AlphaDummy198;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0203 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy185) ≠ (nb067AlphaDummy193) from (by
                                  unfold nb067AlphaDummy193;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0200) 0))))
                              (show (nb067AlphaDummy188 f) ≠ (nb067AlphaDummy194 f) from
                                (by
                                  unfold nb067AlphaDummy194;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0201 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0072`. -/
@[expose]
noncomputable def nb067SplitAlpha0072 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy177), (nb067AlphaDummy179 f)),
        ((nb067AlphaDummy178), (nb067AlphaDummy180 f)),
        ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
        ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
        ((nb067AlphaDummy175), (nb067AlphaDummy176 f)),
        ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
        ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
        ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
        ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
        ((nb067AlphaDummy278), (nb067AlphaDummy280 f)),
        ((nb067AlphaDummy277), (nb067AlphaDummy279 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy177))
          (Class.cv (nb067AlphaDummy170))) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy178))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy177)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy177)) (synC1c))
              (Class.cv (nb067AlphaDummy177))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy179 f))
          (Class.cv (nb067AlphaDummy172 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy180 f))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy179 f)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy179 f)) (synC1c))
              (Class.cv (nb067AlphaDummy179 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067AlphaDummy170) ≠ (nb067AlphaDummy177) from (by
              unfold nb067AlphaDummy177;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0182) 0))))
          (show (nb067AlphaDummy172 f) ≠ (nb067AlphaDummy179 f) from (by
              unfold nb067AlphaDummy179;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0183 f) 0))))
          (TAlphaVar.there (show (nb067AlphaDummy170) ≠ (nb067AlphaDummy178) from (by
                unfold nb067AlphaDummy178;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0182) 1))))
            (show (nb067AlphaDummy172 f) ≠ (nb067AlphaDummy180 f) from (by
                unfold nb067AlphaDummy180;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0183 f) 1))))
            (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy170))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb067AlphaDummy172 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb067AlphaDummy177) ≠ (nb067AlphaDummy184) from (by
                                  unfold nb067AlphaDummy184;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0186) 1))))
                              (show (nb067AlphaDummy179 f) ≠ (nb067AlphaDummy187 f) from
                                (by
                                  unfold nb067AlphaDummy187;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0187 f) 1))))
                              (TAlphaVar.there
                                (show (nb067AlphaDummy177) ≠ (nb067AlphaDummy183) from (by
                                    unfold nb067AlphaDummy183;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0186) 0)))) (show
                                  (nb067AlphaDummy179 f) ≠ (nb067AlphaDummy186 f) from (by
                                    unfold nb067AlphaDummy186;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0187 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb067AlphaDummy177) ≠ (nb067AlphaDummy181) from
                                    (by
                                      unfold nb067AlphaDummy181;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0184)
                                              0)))) (show
                                    (nb067AlphaDummy179 f) ≠ (nb067AlphaDummy182 f) from
                                    (by
                                      unfold nb067AlphaDummy182;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0185 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb067AlphaDummy185), (nb067AlphaDummy188 f)),
                                  ((nb067AlphaDummy184), (nb067AlphaDummy187 f)),
                                  ((nb067AlphaDummy183), (nb067AlphaDummy186 f)),
                                  ((nb067AlphaDummy181), (nb067AlphaDummy182 f)),
                                  ((nb067AlphaDummy177), (nb067AlphaDummy179 f)),
                                  ((nb067AlphaDummy178), (nb067AlphaDummy180 f)),
                                  ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
                                  ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
                                  ((nb067AlphaDummy175), (nb067AlphaDummy176 f)),
                                  ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
                                  ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
                                  ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
                                  ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
                                  ((nb067AlphaDummy278), (nb067AlphaDummy280 f)),
                                  ((nb067AlphaDummy277), (nb067AlphaDummy279 f)),
                                  ((nb067AlphaDummy000), f), ((nb067AlphaDummy003),
                                    (nb067AlphaDummy004 x y f)),
                                  ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                                  ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb067SplitAlpha0071 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb067AlphaDummy177) ≠ (nb067AlphaDummy181) from (by
                          unfold nb067AlphaDummy181;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0184) 0))))
                      (show (nb067AlphaDummy179 f) ≠ (nb067AlphaDummy182 f) from (by
                          unfold nb067AlphaDummy182;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0185 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb067AlphaDummy181), (nb067AlphaDummy182 f)),
                      ((nb067AlphaDummy177), (nb067AlphaDummy179 f)),
                      ((nb067AlphaDummy178), (nb067AlphaDummy180 f)),
                      ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
                      ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
                      ((nb067AlphaDummy175), (nb067AlphaDummy176 f)),
                      ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
                      ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
                      ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
                      ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
                      ((nb067AlphaDummy278), (nb067AlphaDummy280 f)),
                      ((nb067AlphaDummy277), (nb067AlphaDummy279 f)),
                      ((nb067AlphaDummy000), f),
                      ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                      ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                      ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067AlphaDummy177) ≠ (nb067AlphaDummy181) from
                      (by
                        unfold nb067AlphaDummy181;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0184) 0))))
                    (show (nb067AlphaDummy179 f) ≠ (nb067AlphaDummy182 f) from (by
                        unfold nb067AlphaDummy182;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0185 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb067AlphaDummy177) ≠ (nb067AlphaDummy181) from (by
                          unfold nb067AlphaDummy181;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0184) 0))))
                      (show (nb067AlphaDummy179 f) ≠ (nb067AlphaDummy182 f) from (by
                          unfold nb067AlphaDummy182;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0185 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb067AlphaDummy181), (nb067AlphaDummy182 f)),
                      ((nb067AlphaDummy177), (nb067AlphaDummy179 f)),
                      ((nb067AlphaDummy178), (nb067AlphaDummy180 f)),
                      ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
                      ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
                      ((nb067AlphaDummy175), (nb067AlphaDummy176 f)),
                      ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
                      ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
                      ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
                      ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
                      ((nb067AlphaDummy278), (nb067AlphaDummy280 f)),
                      ((nb067AlphaDummy277), (nb067AlphaDummy279 f)),
                      ((nb067AlphaDummy000), f),
                      ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                      ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                      ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part030`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0073`. -/
@[expose]
noncomputable def nb067SplitAlpha0073 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy185), (nb067AlphaDummy188 f)),
        ((nb067AlphaDummy184), (nb067AlphaDummy187 f)),
        ((nb067AlphaDummy183), (nb067AlphaDummy186 f)),
        ((nb067AlphaDummy181), (nb067AlphaDummy182 f)),
        ((nb067AlphaDummy177), (nb067AlphaDummy179 f)),
        ((nb067AlphaDummy178), (nb067AlphaDummy180 f)),
        ((nb067AlphaDummy203), (nb067AlphaDummy204 f)),
        ((nb067AlphaDummy201), (nb067AlphaDummy202 f)),
        ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
        ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
        ((nb067AlphaDummy199), (nb067AlphaDummy200 f)),
        ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
        ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
        ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
        ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
        ((nb067AlphaDummy278), (nb067AlphaDummy280 f)),
        ((nb067AlphaDummy277), (nb067AlphaDummy279 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb067AlphaDummy184)) (Class.cv (nb067AlphaDummy185)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb067AlphaDummy183))
            (synCun (Class.cv (nb067AlphaDummy184)) (Class.cv (nb067AlphaDummy185))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb067AlphaDummy187 f))
            (Class.cv (nb067AlphaDummy188 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy186 f))
            (synCun (Class.cv (nb067AlphaDummy187 f))
              (Class.cv (nb067AlphaDummy188 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy184) ≠ (nb067AlphaDummy191) from (by
                              unfold nb067AlphaDummy191;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0190) 0))))
                          (show (nb067AlphaDummy187 f) ≠ (nb067AlphaDummy192 f) from (by
                              unfold nb067AlphaDummy192;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0191 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy184) ≠ (nb067AlphaDummy189) from (by
                                unfold nb067AlphaDummy189;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0188) 0))))
                            (show (nb067AlphaDummy187 f) ≠ (nb067AlphaDummy190 f) from (by
                                unfold nb067AlphaDummy190;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0189 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy185) ≠ (nb067AlphaDummy191) from (by
                              unfold nb067AlphaDummy191;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0194) 0))))
                          (show (nb067AlphaDummy188 f) ≠ (nb067AlphaDummy192 f) from (by
                              unfold nb067AlphaDummy192;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0195 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy185) ≠ (nb067AlphaDummy189) from (by
                                unfold nb067AlphaDummy189;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0192) 0))))
                            (show (nb067AlphaDummy188 f) ≠ (nb067AlphaDummy190 f) from (by
                                unfold nb067AlphaDummy190;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0193 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy184) ≠ (nb067AlphaDummy191) from (by
                              unfold nb067AlphaDummy191;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0190) 0))))
                          (show (nb067AlphaDummy187 f) ≠ (nb067AlphaDummy192 f) from (by
                              unfold nb067AlphaDummy192;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0191 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy184) ≠ (nb067AlphaDummy189) from (by
                                unfold nb067AlphaDummy189;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0188) 0))))
                            (show (nb067AlphaDummy187 f) ≠ (nb067AlphaDummy190 f) from (by
                                unfold nb067AlphaDummy190;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0189 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy185) ≠ (nb067AlphaDummy191) from (by
                              unfold nb067AlphaDummy191;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0194) 0))))
                          (show (nb067AlphaDummy188 f) ≠ (nb067AlphaDummy192 f) from (by
                              unfold nb067AlphaDummy192;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0195 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy185) ≠ (nb067AlphaDummy189) from (by
                                unfold nb067AlphaDummy189;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0192) 0))))
                            (show (nb067AlphaDummy188 f) ≠ (nb067AlphaDummy190 f) from (by
                                unfold nb067AlphaDummy190;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0193 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb067AlphaDummy185), (nb067AlphaDummy188 f)),
          ((nb067AlphaDummy184), (nb067AlphaDummy187 f)),
          ((nb067AlphaDummy183), (nb067AlphaDummy186 f)),
          ((nb067AlphaDummy181), (nb067AlphaDummy182 f)),
          ((nb067AlphaDummy177), (nb067AlphaDummy179 f)),
          ((nb067AlphaDummy178), (nb067AlphaDummy180 f)),
          ((nb067AlphaDummy203), (nb067AlphaDummy204 f)),
          ((nb067AlphaDummy201), (nb067AlphaDummy202 f)),
          ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
          ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
          ((nb067AlphaDummy199), (nb067AlphaDummy200 f)),
          ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
          ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
          ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
          ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
          ((nb067AlphaDummy278), (nb067AlphaDummy280 f)),
          ((nb067AlphaDummy277), (nb067AlphaDummy279 f)), ((nb067AlphaDummy000), f),
          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy184) ≠ (nb067AlphaDummy195) from (by
                                unfold nb067AlphaDummy195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0198) 0))))
                            (show (nb067AlphaDummy187 f) ≠ (nb067AlphaDummy196 f) from (by
                                unfold nb067AlphaDummy196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0199 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy184) ≠ (nb067AlphaDummy193) from (by
                                  unfold nb067AlphaDummy193;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0196) 0))))
                              (show (nb067AlphaDummy187 f) ≠ (nb067AlphaDummy194 f) from
                                (by
                                  unfold nb067AlphaDummy194;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0197 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy184) ≠ (nb067AlphaDummy195) from (by
                                unfold nb067AlphaDummy195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0198) 0))))
                            (show (nb067AlphaDummy187 f) ≠ (nb067AlphaDummy196 f) from (by
                                unfold nb067AlphaDummy196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0199 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy184) ≠ (nb067AlphaDummy193) from (by
                                  unfold nb067AlphaDummy193;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0196) 0))))
                              (show (nb067AlphaDummy187 f) ≠ (nb067AlphaDummy194 f) from
                                (by
                                  unfold nb067AlphaDummy194;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0197 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy185) ≠ (nb067AlphaDummy197) from (by
                                unfold nb067AlphaDummy197;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0202) 0))))
                            (show (nb067AlphaDummy188 f) ≠ (nb067AlphaDummy198 f) from (by
                                unfold nb067AlphaDummy198;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0203 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy185) ≠ (nb067AlphaDummy193) from (by
                                  unfold nb067AlphaDummy193;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0200) 0))))
                              (show (nb067AlphaDummy188 f) ≠ (nb067AlphaDummy194 f) from
                                (by
                                  unfold nb067AlphaDummy194;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0201 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy185) ≠ (nb067AlphaDummy197) from (by
                                unfold nb067AlphaDummy197;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0202) 0))))
                            (show (nb067AlphaDummy188 f) ≠ (nb067AlphaDummy198 f) from (by
                                unfold nb067AlphaDummy198;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0203 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy185) ≠ (nb067AlphaDummy193) from (by
                                  unfold nb067AlphaDummy193;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0200) 0))))
                              (show (nb067AlphaDummy188 f) ≠ (nb067AlphaDummy194 f) from
                                (by
                                  unfold nb067AlphaDummy194;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0201 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0074`. -/
@[expose]
noncomputable def nb067SplitAlpha0074 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy177), (nb067AlphaDummy179 f)),
        ((nb067AlphaDummy178), (nb067AlphaDummy180 f)),
        ((nb067AlphaDummy203), (nb067AlphaDummy204 f)),
        ((nb067AlphaDummy201), (nb067AlphaDummy202 f)),
        ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
        ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
        ((nb067AlphaDummy199), (nb067AlphaDummy200 f)),
        ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
        ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
        ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
        ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
        ((nb067AlphaDummy278), (nb067AlphaDummy280 f)),
        ((nb067AlphaDummy277), (nb067AlphaDummy279 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy177))
          (Class.cv (nb067AlphaDummy170))) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy178))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy177)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy177)) (synC1c))
              (Class.cv (nb067AlphaDummy177))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy179 f))
          (Class.cv (nb067AlphaDummy172 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy180 f))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy179 f)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy179 f)) (synC1c))
              (Class.cv (nb067AlphaDummy179 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067AlphaDummy170) ≠ (nb067AlphaDummy177) from (by
              unfold nb067AlphaDummy177;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0182) 0))))
          (show (nb067AlphaDummy172 f) ≠ (nb067AlphaDummy179 f) from (by
              unfold nb067AlphaDummy179;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0183 f) 0))))
          (TAlphaVar.there (show (nb067AlphaDummy170) ≠ (nb067AlphaDummy178) from (by
                unfold nb067AlphaDummy178;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0182) 1))))
            (show (nb067AlphaDummy172 f) ≠ (nb067AlphaDummy180 f) from (by
                unfold nb067AlphaDummy180;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0183 f) 1))))
            (TAlphaVar.there (show (nb067AlphaDummy170) ≠ (nb067AlphaDummy203) from (by
                  unfold nb067AlphaDummy203;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0212) 0))))
              (show (nb067AlphaDummy172 f) ≠ (nb067AlphaDummy204 f) from (by
                  unfold nb067AlphaDummy204;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0213 f) 0))))
              (TAlphaVar.there (show (nb067AlphaDummy170) ≠ (nb067AlphaDummy201) from (by
                    unfold nb067AlphaDummy201;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0210) 0))))
                (show (nb067AlphaDummy172 f) ≠ (nb067AlphaDummy202 f) from (by
                    unfold nb067AlphaDummy202;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0211 f) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy170))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb067AlphaDummy172 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb067AlphaDummy177) ≠ (nb067AlphaDummy184) from (by
                                  unfold nb067AlphaDummy184;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0186) 1))))
                              (show (nb067AlphaDummy179 f) ≠ (nb067AlphaDummy187 f) from
                                (by
                                  unfold nb067AlphaDummy187;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0187 f) 1))))
                              (TAlphaVar.there
                                (show (nb067AlphaDummy177) ≠ (nb067AlphaDummy183) from (by
                                    unfold nb067AlphaDummy183;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0186) 0)))) (show
                                  (nb067AlphaDummy179 f) ≠ (nb067AlphaDummy186 f) from (by
                                    unfold nb067AlphaDummy186;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0187 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb067AlphaDummy177) ≠ (nb067AlphaDummy181) from
                                    (by
                                      unfold nb067AlphaDummy181;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0184)
                                              0)))) (show
                                    (nb067AlphaDummy179 f) ≠ (nb067AlphaDummy182 f) from
                                    (by
                                      unfold nb067AlphaDummy182;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0185 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb067AlphaDummy185), (nb067AlphaDummy188 f)),
                                  ((nb067AlphaDummy184), (nb067AlphaDummy187 f)),
                                  ((nb067AlphaDummy183), (nb067AlphaDummy186 f)),
                                  ((nb067AlphaDummy181), (nb067AlphaDummy182 f)),
                                  ((nb067AlphaDummy177), (nb067AlphaDummy179 f)),
                                  ((nb067AlphaDummy178), (nb067AlphaDummy180 f)),
                                  ((nb067AlphaDummy203), (nb067AlphaDummy204 f)),
                                  ((nb067AlphaDummy201), (nb067AlphaDummy202 f)),
                                  ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
                                  ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
                                  ((nb067AlphaDummy199), (nb067AlphaDummy200 f)),
                                  ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
                                  ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
                                  ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
                                  ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
                                  ((nb067AlphaDummy278), (nb067AlphaDummy280 f)),
                                  ((nb067AlphaDummy277), (nb067AlphaDummy279 f)),
                                  ((nb067AlphaDummy000), f), ((nb067AlphaDummy003),
                                    (nb067AlphaDummy004 x y f)),
                                  ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                                  ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb067SplitAlpha0073 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb067AlphaDummy177) ≠ (nb067AlphaDummy181) from (by
                          unfold nb067AlphaDummy181;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0184) 0))))
                      (show (nb067AlphaDummy179 f) ≠ (nb067AlphaDummy182 f) from (by
                          unfold nb067AlphaDummy182;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0185 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb067AlphaDummy181), (nb067AlphaDummy182 f)),
                      ((nb067AlphaDummy177), (nb067AlphaDummy179 f)),
                      ((nb067AlphaDummy178), (nb067AlphaDummy180 f)),
                      ((nb067AlphaDummy203), (nb067AlphaDummy204 f)),
                      ((nb067AlphaDummy201), (nb067AlphaDummy202 f)),
                      ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
                      ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
                      ((nb067AlphaDummy199), (nb067AlphaDummy200 f)),
                      ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
                      ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
                      ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
                      ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
                      ((nb067AlphaDummy278), (nb067AlphaDummy280 f)),
                      ((nb067AlphaDummy277), (nb067AlphaDummy279 f)),
                      ((nb067AlphaDummy000), f),
                      ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                      ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                      ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067AlphaDummy177) ≠ (nb067AlphaDummy181) from
                      (by
                        unfold nb067AlphaDummy181;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0184) 0))))
                    (show (nb067AlphaDummy179 f) ≠ (nb067AlphaDummy182 f) from (by
                        unfold nb067AlphaDummy182;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0185 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb067AlphaDummy177) ≠ (nb067AlphaDummy181) from (by
                          unfold nb067AlphaDummy181;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0184) 0))))
                      (show (nb067AlphaDummy179 f) ≠ (nb067AlphaDummy182 f) from (by
                          unfold nb067AlphaDummy182;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0185 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb067AlphaDummy181), (nb067AlphaDummy182 f)),
                      ((nb067AlphaDummy177), (nb067AlphaDummy179 f)),
                      ((nb067AlphaDummy178), (nb067AlphaDummy180 f)),
                      ((nb067AlphaDummy203), (nb067AlphaDummy204 f)),
                      ((nb067AlphaDummy201), (nb067AlphaDummy202 f)),
                      ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
                      ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
                      ((nb067AlphaDummy199), (nb067AlphaDummy200 f)),
                      ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
                      ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
                      ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
                      ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
                      ((nb067AlphaDummy278), (nb067AlphaDummy280 f)),
                      ((nb067AlphaDummy277), (nb067AlphaDummy279 f)),
                      ((nb067AlphaDummy000), f),
                      ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                      ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                      ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0075`. -/
@[expose]
noncomputable def nb067SplitAlpha0075 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy199), (nb067AlphaDummy200 f)),
        ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
        ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
        ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
        ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
        ((nb067AlphaDummy278), (nb067AlphaDummy280 f)),
        ((nb067AlphaDummy277), (nb067AlphaDummy279 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy199))
          (Class.cab (nb067AlphaDummy169)
            (synWrex (nb067AlphaDummy170) (Class.cv (nb067AlphaDummy164))
              (Wff.classEq (Class.cv (nb067AlphaDummy169))
                (synCun (synCphi (Class.cv (nb067AlphaDummy170))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb067AlphaDummy199))
            (Class.cab (nb067AlphaDummy169)
              (synWrex (nb067AlphaDummy170) (Class.cv (nb067AlphaDummy164))
                (Wff.classEq (Class.cv (nb067AlphaDummy169))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy170)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy200 f))
          (Class.cab (nb067AlphaDummy171 f)
            (synWrex (nb067AlphaDummy172 f) (Class.cv (nb067AlphaDummy166 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy171 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy172 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb067AlphaDummy200 f))
            (Class.cab (nb067AlphaDummy171 f)
              (synWrex (nb067AlphaDummy172 f) (Class.cv (nb067AlphaDummy166 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy171 f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy172 f)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb067AlphaDummy164) ≠ (nb067AlphaDummy170) from
                    (by
                      unfold nb067AlphaDummy170;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0204) 1))))
                  (show (nb067AlphaDummy166 f) ≠ (nb067AlphaDummy172 f) from (by
                      unfold nb067AlphaDummy172;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0206 f) 1))))
                  (TAlphaVar.there (show (nb067AlphaDummy164) ≠ (nb067AlphaDummy169) from
                      (by
                        unfold nb067AlphaDummy169;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0204) 0))))
                    (show (nb067AlphaDummy166 f) ≠ (nb067AlphaDummy171 f) from (by
                        unfold nb067AlphaDummy171;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0206 f) 0)))) (TAlphaVar.there
                      (show (nb067AlphaDummy164) ≠ (nb067AlphaDummy199) from (by
                          unfold nb067AlphaDummy199;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0208) 0))))
                      (show (nb067AlphaDummy166 f) ≠ (nb067AlphaDummy200 f) from (by
                          unfold nb067AlphaDummy200;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0209 f) 0))))
                      (TAlphaVar.there
                        (show (nb067AlphaDummy164) ≠ (nb067AlphaDummy173) from (by
                            unfold nb067AlphaDummy173;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0205) 0))))
                        (show (nb067AlphaDummy166 f) ≠ (nb067AlphaDummy174 f) from (by
                            unfold nb067AlphaDummy174;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0207 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb067AlphaDummy163))).fv ∪
                      ((Class.cv (nb067AlphaDummy164))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb067AlphaDummy165 f))).fv ∪
                      ((Class.cv (nb067AlphaDummy166 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067SplitAlpha0074 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067SplitAlpha0074 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb067AlphaDummy201), (nb067AlphaDummy202 f)),
                          ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
                          ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
                          ((nb067AlphaDummy199), (nb067AlphaDummy200 f)),
                          ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
                          ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
                          ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
                          ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
                          ((nb067AlphaDummy278), (nb067AlphaDummy280 f)),
                          ((nb067AlphaDummy277), (nb067AlphaDummy279 f)),
                          ((nb067AlphaDummy000), f),
                          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067AlphaDummy164) ≠ (nb067AlphaDummy170) from
                      (by
                        unfold nb067AlphaDummy170;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0204) 1))))
                    (show (nb067AlphaDummy166 f) ≠ (nb067AlphaDummy172 f) from (by
                        unfold nb067AlphaDummy172;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0206 f) 1)))) (TAlphaVar.there
                      (show (nb067AlphaDummy164) ≠ (nb067AlphaDummy169) from (by
                          unfold nb067AlphaDummy169;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0204) 0))))
                      (show (nb067AlphaDummy166 f) ≠ (nb067AlphaDummy171 f) from (by
                          unfold nb067AlphaDummy171;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0206 f) 0))))
                      (TAlphaVar.there
                        (show (nb067AlphaDummy164) ≠ (nb067AlphaDummy199) from (by
                            unfold nb067AlphaDummy199;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0208) 0))))
                        (show (nb067AlphaDummy166 f) ≠ (nb067AlphaDummy200 f) from (by
                            unfold nb067AlphaDummy200;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0209 f) 0))))
                        (TAlphaVar.there
                          (show (nb067AlphaDummy164) ≠ (nb067AlphaDummy173) from (by
                              unfold nb067AlphaDummy173;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0205) 0))))
                          (show (nb067AlphaDummy166 f) ≠ (nb067AlphaDummy174 f) from (by
                              unfold nb067AlphaDummy174;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0207 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb067AlphaDummy163))).fv ∪
                        ((Class.cv (nb067AlphaDummy164))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb067AlphaDummy165 f))).fv ∪
                        ((Class.cv (nb067AlphaDummy166 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067SplitAlpha0074 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067SplitAlpha0074 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb067AlphaDummy201), (nb067AlphaDummy202 f)),
                            ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
                            ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
                            ((nb067AlphaDummy199), (nb067AlphaDummy200 f)),
                            ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
                            ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
                            ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
                            ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
                            ((nb067AlphaDummy278), (nb067AlphaDummy280 f)),
                            ((nb067AlphaDummy277), (nb067AlphaDummy279 f)),
                            ((nb067AlphaDummy000), f),
                            ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                            ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                            ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0076`. -/
@[expose]
noncomputable def nb067SplitAlpha0076 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy221), (nb067AlphaDummy224 f)),
        ((nb067AlphaDummy220), (nb067AlphaDummy223 f)),
        ((nb067AlphaDummy219), (nb067AlphaDummy222 f)),
        ((nb067AlphaDummy217), (nb067AlphaDummy218 f)),
        ((nb067AlphaDummy213), (nb067AlphaDummy215 f)),
        ((nb067AlphaDummy214), (nb067AlphaDummy216 f)),
        ((nb067AlphaDummy206), (nb067AlphaDummy208 f)),
        ((nb067AlphaDummy205), (nb067AlphaDummy207 f)),
        ((nb067AlphaDummy211), (nb067AlphaDummy212 f)),
        ((nb067AlphaDummy209), (nb067AlphaDummy210 f)),
        ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
        ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
        ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
        ((nb067AlphaDummy278), (nb067AlphaDummy280 f)),
        ((nb067AlphaDummy277), (nb067AlphaDummy279 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb067AlphaDummy220)) (Class.cv (nb067AlphaDummy221)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb067AlphaDummy219))
            (synCun (Class.cv (nb067AlphaDummy220)) (Class.cv (nb067AlphaDummy221))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb067AlphaDummy223 f))
            (Class.cv (nb067AlphaDummy224 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy222 f))
            (synCun (Class.cv (nb067AlphaDummy223 f))
              (Class.cv (nb067AlphaDummy224 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy220) ≠ (nb067AlphaDummy227) from (by
                              unfold nb067AlphaDummy227;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0228) 0))))
                          (show (nb067AlphaDummy223 f) ≠ (nb067AlphaDummy228 f) from (by
                              unfold nb067AlphaDummy228;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0229 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy220) ≠ (nb067AlphaDummy225) from (by
                                unfold nb067AlphaDummy225;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0226) 0))))
                            (show (nb067AlphaDummy223 f) ≠ (nb067AlphaDummy226 f) from (by
                                unfold nb067AlphaDummy226;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0227 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy221) ≠ (nb067AlphaDummy227) from (by
                              unfold nb067AlphaDummy227;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0232) 0))))
                          (show (nb067AlphaDummy224 f) ≠ (nb067AlphaDummy228 f) from (by
                              unfold nb067AlphaDummy228;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0233 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy221) ≠ (nb067AlphaDummy225) from (by
                                unfold nb067AlphaDummy225;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0230) 0))))
                            (show (nb067AlphaDummy224 f) ≠ (nb067AlphaDummy226 f) from (by
                                unfold nb067AlphaDummy226;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0231 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy220) ≠ (nb067AlphaDummy227) from (by
                              unfold nb067AlphaDummy227;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0228) 0))))
                          (show (nb067AlphaDummy223 f) ≠ (nb067AlphaDummy228 f) from (by
                              unfold nb067AlphaDummy228;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0229 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy220) ≠ (nb067AlphaDummy225) from (by
                                unfold nb067AlphaDummy225;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0226) 0))))
                            (show (nb067AlphaDummy223 f) ≠ (nb067AlphaDummy226 f) from (by
                                unfold nb067AlphaDummy226;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0227 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy221) ≠ (nb067AlphaDummy227) from (by
                              unfold nb067AlphaDummy227;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0232) 0))))
                          (show (nb067AlphaDummy224 f) ≠ (nb067AlphaDummy228 f) from (by
                              unfold nb067AlphaDummy228;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0233 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy221) ≠ (nb067AlphaDummy225) from (by
                                unfold nb067AlphaDummy225;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0230) 0))))
                            (show (nb067AlphaDummy224 f) ≠ (nb067AlphaDummy226 f) from (by
                                unfold nb067AlphaDummy226;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0231 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb067AlphaDummy221), (nb067AlphaDummy224 f)),
          ((nb067AlphaDummy220), (nb067AlphaDummy223 f)),
          ((nb067AlphaDummy219), (nb067AlphaDummy222 f)),
          ((nb067AlphaDummy217), (nb067AlphaDummy218 f)),
          ((nb067AlphaDummy213), (nb067AlphaDummy215 f)),
          ((nb067AlphaDummy214), (nb067AlphaDummy216 f)),
          ((nb067AlphaDummy206), (nb067AlphaDummy208 f)),
          ((nb067AlphaDummy205), (nb067AlphaDummy207 f)),
          ((nb067AlphaDummy211), (nb067AlphaDummy212 f)),
          ((nb067AlphaDummy209), (nb067AlphaDummy210 f)),
          ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
          ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
          ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
          ((nb067AlphaDummy278), (nb067AlphaDummy280 f)),
          ((nb067AlphaDummy277), (nb067AlphaDummy279 f)), ((nb067AlphaDummy000), f),
          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy220) ≠ (nb067AlphaDummy231) from (by
                                unfold nb067AlphaDummy231;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0236) 0))))
                            (show (nb067AlphaDummy223 f) ≠ (nb067AlphaDummy232 f) from (by
                                unfold nb067AlphaDummy232;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0237 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy220) ≠ (nb067AlphaDummy229) from (by
                                  unfold nb067AlphaDummy229;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0234) 0))))
                              (show (nb067AlphaDummy223 f) ≠ (nb067AlphaDummy230 f) from
                                (by
                                  unfold nb067AlphaDummy230;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0235 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy220) ≠ (nb067AlphaDummy231) from (by
                                unfold nb067AlphaDummy231;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0236) 0))))
                            (show (nb067AlphaDummy223 f) ≠ (nb067AlphaDummy232 f) from (by
                                unfold nb067AlphaDummy232;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0237 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy220) ≠ (nb067AlphaDummy229) from (by
                                  unfold nb067AlphaDummy229;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0234) 0))))
                              (show (nb067AlphaDummy223 f) ≠ (nb067AlphaDummy230 f) from
                                (by
                                  unfold nb067AlphaDummy230;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0235 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy221) ≠ (nb067AlphaDummy233) from (by
                                unfold nb067AlphaDummy233;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0240) 0))))
                            (show (nb067AlphaDummy224 f) ≠ (nb067AlphaDummy234 f) from (by
                                unfold nb067AlphaDummy234;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0241 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy221) ≠ (nb067AlphaDummy229) from (by
                                  unfold nb067AlphaDummy229;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0238) 0))))
                              (show (nb067AlphaDummy224 f) ≠ (nb067AlphaDummy230 f) from
                                (by
                                  unfold nb067AlphaDummy230;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0239 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy221) ≠ (nb067AlphaDummy233) from (by
                                unfold nb067AlphaDummy233;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0240) 0))))
                            (show (nb067AlphaDummy224 f) ≠ (nb067AlphaDummy234 f) from (by
                                unfold nb067AlphaDummy234;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0241 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy221) ≠ (nb067AlphaDummy229) from (by
                                  unfold nb067AlphaDummy229;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0238) 0))))
                              (show (nb067AlphaDummy224 f) ≠ (nb067AlphaDummy230 f) from
                                (by
                                  unfold nb067AlphaDummy230;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0239 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
