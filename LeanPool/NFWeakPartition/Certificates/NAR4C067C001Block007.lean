/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C067C001Block006

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C067C001Part031`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0077`. -/
@[expose]
noncomputable def nb067SplitAlpha0077 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy213), (nb067AlphaDummy215 f)),
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
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy213))
          (Class.cv (nb067AlphaDummy206))) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy214))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy213)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy213)) (synC1c))
              (Class.cv (nb067AlphaDummy213))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy215 f))
          (Class.cv (nb067AlphaDummy208 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy216 f))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy215 f)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy215 f)) (synC1c))
              (Class.cv (nb067AlphaDummy215 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067AlphaDummy206) ≠ (nb067AlphaDummy213) from (by
              unfold nb067AlphaDummy213;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0220) 0))))
          (show (nb067AlphaDummy208 f) ≠ (nb067AlphaDummy215 f) from (by
              unfold nb067AlphaDummy215;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0221 f) 0))))
          (TAlphaVar.there (show (nb067AlphaDummy206) ≠ (nb067AlphaDummy214) from (by
                unfold nb067AlphaDummy214;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0220) 1))))
            (show (nb067AlphaDummy208 f) ≠ (nb067AlphaDummy216 f) from (by
                unfold nb067AlphaDummy216;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0221 f) 1))))
            (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy206))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb067AlphaDummy208 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb067AlphaDummy213) ≠ (nb067AlphaDummy220) from (by
                                  unfold nb067AlphaDummy220;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0224) 1))))
                              (show (nb067AlphaDummy215 f) ≠ (nb067AlphaDummy223 f) from
                                (by
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
                                          (mem_lt_freshVar (nb067_support_mem_0224) 0)))) (show
                                  (nb067AlphaDummy215 f) ≠ (nb067AlphaDummy222 f) from (by
                                    unfold nb067AlphaDummy222;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0225 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb067AlphaDummy213) ≠ (nb067AlphaDummy217) from
                                    (by
                                      unfold nb067AlphaDummy217;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0222)
                                              0)))) (show
                                    (nb067AlphaDummy215 f) ≠ (nb067AlphaDummy218 f) from
                                    (by
                                      unfold nb067AlphaDummy218;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0223 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
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
                                  ((nb067AlphaDummy000), f), ((nb067AlphaDummy003),
                                    (nb067AlphaDummy004 x y f)),
                                  ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                                  ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb067SplitAlpha0076 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb067AlphaDummy213) ≠ (nb067AlphaDummy217) from (by
                          unfold nb067AlphaDummy217;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0222) 0))))
                      (show (nb067AlphaDummy215 f) ≠ (nb067AlphaDummy218 f) from (by
                          unfold nb067AlphaDummy218;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0223 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb067AlphaDummy217), (nb067AlphaDummy218 f)),
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
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
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
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0223 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb067AlphaDummy213) ≠ (nb067AlphaDummy217) from (by
                          unfold nb067AlphaDummy217;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0222) 0))))
                      (show (nb067AlphaDummy215 f) ≠ (nb067AlphaDummy218 f) from (by
                          unfold nb067AlphaDummy218;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0223 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb067AlphaDummy217), (nb067AlphaDummy218 f)),
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
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0078`. -/
@[expose]
noncomputable def nb067SplitAlpha0078 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
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
          ((nb067AlphaDummy239), (nb067AlphaDummy240 f)),
          ((nb067AlphaDummy237), (nb067AlphaDummy238 f)),
          ((nb067AlphaDummy206), (nb067AlphaDummy208 f)),
          ((nb067AlphaDummy205), (nb067AlphaDummy207 f)),
          ((nb067AlphaDummy235), (nb067AlphaDummy236 f)),
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

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0079`. -/
@[expose]
noncomputable def nb067SplitAlpha0079 (x : Var) (y : Var) (f : Var) :
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
        ((nb067AlphaDummy278), (nb067AlphaDummy280 f)),
        ((nb067AlphaDummy277), (nb067AlphaDummy279 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy213))
          (Class.cv (nb067AlphaDummy206))) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy214))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy213)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy213)) (synC1c))
              (Class.cv (nb067AlphaDummy213))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy215 f))
          (Class.cv (nb067AlphaDummy208 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy216 f))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy215 f)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy215 f)) (synC1c))
              (Class.cv (nb067AlphaDummy215 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067AlphaDummy206) ≠ (nb067AlphaDummy213) from (by
              unfold nb067AlphaDummy213;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0220) 0))))
          (show (nb067AlphaDummy208 f) ≠ (nb067AlphaDummy215 f) from (by
              unfold nb067AlphaDummy215;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0221 f) 0))))
          (TAlphaVar.there (show (nb067AlphaDummy206) ≠ (nb067AlphaDummy214) from (by
                unfold nb067AlphaDummy214;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0220) 1))))
            (show (nb067AlphaDummy208 f) ≠ (nb067AlphaDummy216 f) from (by
                unfold nb067AlphaDummy216;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0221 f) 1))))
            (TAlphaVar.there (show (nb067AlphaDummy206) ≠ (nb067AlphaDummy239) from (by
                  unfold nb067AlphaDummy239;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0250) 0))))
              (show (nb067AlphaDummy208 f) ≠ (nb067AlphaDummy240 f) from (by
                  unfold nb067AlphaDummy240;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0251 f) 0))))
              (TAlphaVar.there (show (nb067AlphaDummy206) ≠ (nb067AlphaDummy237) from (by
                    unfold nb067AlphaDummy237;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0248) 0))))
                (show (nb067AlphaDummy208 f) ≠ (nb067AlphaDummy238 f) from (by
                    unfold nb067AlphaDummy238;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0249 f) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy206))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb067AlphaDummy208 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb067AlphaDummy213) ≠ (nb067AlphaDummy220) from (by
                                  unfold nb067AlphaDummy220;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0224) 1))))
                              (show (nb067AlphaDummy215 f) ≠ (nb067AlphaDummy223 f) from
                                (by
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
                                          (mem_lt_freshVar (nb067_support_mem_0224) 0)))) (show
                                  (nb067AlphaDummy215 f) ≠ (nb067AlphaDummy222 f) from (by
                                    unfold nb067AlphaDummy222;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0225 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb067AlphaDummy213) ≠ (nb067AlphaDummy217) from
                                    (by
                                      unfold nb067AlphaDummy217;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0222)
                                              0)))) (show
                                    (nb067AlphaDummy215 f) ≠ (nb067AlphaDummy218 f) from
                                    (by
                                      unfold nb067AlphaDummy218;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0223 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
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
                                  ((nb067AlphaDummy278), (nb067AlphaDummy280 f)),
                                  ((nb067AlphaDummy277), (nb067AlphaDummy279 f)),
                                  ((nb067AlphaDummy000), f), ((nb067AlphaDummy003),
                                    (nb067AlphaDummy004 x y f)),
                                  ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                                  ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb067SplitAlpha0078 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb067AlphaDummy213) ≠ (nb067AlphaDummy217) from (by
                          unfold nb067AlphaDummy217;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0222) 0))))
                      (show (nb067AlphaDummy215 f) ≠ (nb067AlphaDummy218 f) from (by
                          unfold nb067AlphaDummy218;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0223 f) 0))))
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
                      ((nb067AlphaDummy278), (nb067AlphaDummy280 f)),
                      ((nb067AlphaDummy277), (nb067AlphaDummy279 f)),
                      ((nb067AlphaDummy000), f),
                      ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                      ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                      ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
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
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0223 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb067AlphaDummy213) ≠ (nb067AlphaDummy217) from (by
                          unfold nb067AlphaDummy217;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0222) 0))))
                      (show (nb067AlphaDummy215 f) ≠ (nb067AlphaDummy218 f) from (by
                          unfold nb067AlphaDummy218;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0223 f) 0))))
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
                      ((nb067AlphaDummy278), (nb067AlphaDummy280 f)),
                      ((nb067AlphaDummy277), (nb067AlphaDummy279 f)),
                      ((nb067AlphaDummy000), f),
                      ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                      ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                      ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0080`. -/
@[expose]
noncomputable def nb067SplitAlpha0080 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy235), (nb067AlphaDummy236 f)),
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
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067SplitAlpha0079 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067SplitAlpha0079 x y f)))))))))
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
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067SplitAlpha0079 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067SplitAlpha0079 x y f)))))))))
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
                            ((nb067AlphaDummy278), (nb067AlphaDummy280 f)),
                            ((nb067AlphaDummy277), (nb067AlphaDummy279 f)),
                            ((nb067AlphaDummy000), f),
                            ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                            ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                            ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0081`. -/
@[expose]
noncomputable def nb067SplitAlpha0081 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
        ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
        ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
        ((nb067AlphaDummy278), (nb067AlphaDummy280 f)),
        ((nb067AlphaDummy277), (nb067AlphaDummy279 f)),
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
                                  (TAlphaWff.neg (nb067SplitAlpha0072 x y f)))))))))
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
                                  (TAlphaWff.neg (nb067SplitAlpha0072 x y f)))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb067SplitAlpha0075 x y f)))))))))
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
                                    (TAlphaWff.neg (nb067SplitAlpha0077 x y f)))))))))
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
                                    (TAlphaWff.neg (nb067SplitAlpha0077 x y f)))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb067SplitAlpha0080 x y f))))))))
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
                (TAlphaVar.there (show (nb067AlphaDummy000) ≠ (nb067AlphaDummy278) from
                    (by
                      unfold nb067AlphaDummy278;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0340) 1))))
                  (show f ≠ (nb067AlphaDummy280 f) from (by
                      unfold nb067AlphaDummy280;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0341 f) 1))))
                  (TAlphaVar.there (show (nb067AlphaDummy000) ≠ (nb067AlphaDummy277) from
                      (by
                        unfold nb067AlphaDummy277;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0340) 0))))
                    (show f ≠ (nb067AlphaDummy279 f) from (by
                        unfold nb067AlphaDummy279;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0341 f) 0))))
                    (TAlphaVar.here _ _ _))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part032`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0082`. -/
@[expose]
noncomputable def nb067SplitAlpha0082 (x : Var) (y : Var) (f : Var) (dv_f_y : f ≠ y) :
    TAlphaWff
      [((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (synWfun (Class.cv (nb067AlphaDummy000))) (Wff.neg
          (Wff.classEq (synCdm (Class.cv (nb067AlphaDummy000)))
            (Class.cv (nb067AlphaDummy002)))))
      (Wff.imp (synWfun (Class.cv f))
        (Wff.neg (Wff.classEq (synCdm (Class.cv f)) (Class.cv y)))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (nb067SplitAlpha0038 x y f))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (nb067SplitAlpha0038 x y f))))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
                      (show (nb067AlphaDummy084) ≠ (nb067AlphaDummy089) from (by
                          unfold nb067AlphaDummy089;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0094) 0))))) (Ne.symm
                      (show (nb067AlphaDummy087 f) ≠ (nb067AlphaDummy090 f) from (by
                          unfold nb067AlphaDummy090;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0095 f) 0)))))
                    (TAlphaVar.there (Ne.symm
                        (show (nb067AlphaDummy083) ≠ (nb067AlphaDummy089) from (by
                            unfold nb067AlphaDummy089;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0092) 0))))) (Ne.symm
                        (show (nb067AlphaDummy086 f) ≠ (nb067AlphaDummy090 f) from (by
                            unfold nb067AlphaDummy090;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0093 f) 0)))))
                      (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067AlphaDummy083) ≠ (nb067AlphaDummy092) from (by
          unfold nb067AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0096) 1)))) (show (nb067AlphaDummy086 f) ≠
        (nb067AlphaDummy094 f) from (by
          unfold nb067AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0098 f) 1)))) (TAlphaVar.there (show
        (nb067AlphaDummy083) ≠ (nb067AlphaDummy091) from (by
          unfold nb067AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0096) 0)))) (show (nb067AlphaDummy086 f) ≠
        (nb067AlphaDummy093 f) from (by
          unfold nb067AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0098 f) 0)))) (TAlphaVar.there (show
        (nb067AlphaDummy083) ≠ (nb067AlphaDummy097) from (by
          unfold nb067AlphaDummy097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0100) 0)))) (show (nb067AlphaDummy086 f) ≠
        (nb067AlphaDummy098 f) from (by
          unfold nb067AlphaDummy098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0101 f)
                  0)))) (TAlphaVar.there (show (nb067AlphaDummy083) ≠ (nb067AlphaDummy095)
        from (by
          unfold nb067AlphaDummy095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0097)
                  0)))) (show (nb067AlphaDummy086 f) ≠ (nb067AlphaDummy096 f) from (by
          unfold nb067AlphaDummy096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0099 f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb067AlphaDummy000))).fv ∪ ((synCcnv (Class.cv (nb067AlphaDummy000)))).fv)
        (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (nb067SplitAlpha0040 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067AlphaDummy083) ≠ (nb067AlphaDummy092) from (by
          unfold nb067AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0096) 1)))) (show (nb067AlphaDummy086 f) ≠
        (nb067AlphaDummy094 f) from (by
          unfold nb067AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0098 f) 1)))) (TAlphaVar.there (show
        (nb067AlphaDummy083) ≠ (nb067AlphaDummy091) from (by
          unfold nb067AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0096) 0)))) (show (nb067AlphaDummy086 f) ≠
        (nb067AlphaDummy093 f) from (by
          unfold nb067AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0098 f) 0)))) (TAlphaVar.there (show
        (nb067AlphaDummy083) ≠ (nb067AlphaDummy097) from (by
          unfold nb067AlphaDummy097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0100) 0)))) (show (nb067AlphaDummy086 f) ≠
        (nb067AlphaDummy098 f) from (by
          unfold nb067AlphaDummy098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0101 f)
                  0)))) (TAlphaVar.there (show (nb067AlphaDummy083) ≠ (nb067AlphaDummy095)
        from (by
          unfold nb067AlphaDummy095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0097)
                  0)))) (show (nb067AlphaDummy086 f) ≠ (nb067AlphaDummy096 f) from (by
          unfold nb067AlphaDummy096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0099 f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb067AlphaDummy000))).fv ∪ ((synCcnv (Class.cv (nb067AlphaDummy000)))).fv)
        (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (nb067SplitAlpha0040 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg
                            (TAlphaWff.neg (nb067SplitAlpha0043 x y f)))))))))
              (TAlphaWff.ex (TAlphaWff.neg (nb067SplitAlpha0065 x y f)))))))) (TAlphaWff.neg
      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb067AlphaDummy278), (nb067AlphaDummy280 f)),
                    ((nb067AlphaDummy277), (nb067AlphaDummy279 f)),
                    ((nb067AlphaDummy000), f),
                    ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                    ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                    ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                  (synCvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067AlphaDummy278) ≠ (nb067AlphaDummy282) from (by
          unfold nb067AlphaDummy282;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0302) 1)))) (show (nb067AlphaDummy280 f) ≠
        (nb067AlphaDummy284 f) from (by
          unfold nb067AlphaDummy284;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0304 f) 1)))) (TAlphaVar.there (show
        (nb067AlphaDummy278) ≠ (nb067AlphaDummy281) from (by
          unfold nb067AlphaDummy281;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0302) 0)))) (show (nb067AlphaDummy280 f) ≠
        (nb067AlphaDummy283 f) from (by
          unfold nb067AlphaDummy283;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0304 f) 0)))) (TAlphaVar.there (show
        (nb067AlphaDummy278) ≠ (nb067AlphaDummy287) from (by
          unfold nb067AlphaDummy287;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0306) 0)))) (show (nb067AlphaDummy280 f) ≠
        (nb067AlphaDummy288 f) from (by
          unfold nb067AlphaDummy288;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0307 f)
                  0)))) (TAlphaVar.there (show (nb067AlphaDummy278) ≠ (nb067AlphaDummy285)
        from (by
          unfold nb067AlphaDummy285;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0303)
                  0)))) (show (nb067AlphaDummy280 f) ≠ (nb067AlphaDummy286 f) from (by
          unfold nb067AlphaDummy286;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0305 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb067SplitAlpha0067 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067AlphaDummy278) ≠ (nb067AlphaDummy282) from (by
          unfold nb067AlphaDummy282;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0302) 1)))) (show (nb067AlphaDummy280 f) ≠
        (nb067AlphaDummy284 f) from (by
          unfold nb067AlphaDummy284;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0304 f) 1)))) (TAlphaVar.there (show
        (nb067AlphaDummy278) ≠ (nb067AlphaDummy281) from (by
          unfold nb067AlphaDummy281;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0302) 0)))) (show (nb067AlphaDummy280 f) ≠
        (nb067AlphaDummy283 f) from (by
          unfold nb067AlphaDummy283;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0304 f) 0)))) (TAlphaVar.there (show
        (nb067AlphaDummy278) ≠ (nb067AlphaDummy287) from (by
          unfold nb067AlphaDummy287;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0306) 0)))) (show (nb067AlphaDummy280 f) ≠
        (nb067AlphaDummy288 f) from (by
          unfold nb067AlphaDummy288;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0307 f)
                  0)))) (TAlphaVar.there (show (nb067AlphaDummy278) ≠ (nb067AlphaDummy285)
        from (by
          unfold nb067AlphaDummy285;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0303)
                  0)))) (show (nb067AlphaDummy280 f) ≠ (nb067AlphaDummy286 f) from (by
          unfold nb067AlphaDummy286;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0305 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb067SplitAlpha0067 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg
                            (TAlphaWff.neg (nb067SplitAlpha0070 x y f))))))))
                (TAlphaClass.cab (TAlphaWff.ex
                    (TAlphaWff.ex (TAlphaWff.neg (nb067SplitAlpha0081 x y f)))))))))
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
            (Ne.symm dv_f_y) (TAlphaVar.there
              (show (nb067AlphaDummy002) ≠ (nb067AlphaDummy003) from (by
                  unfold nb067AlphaDummy003;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0042) 0))))
              (show y ≠ (nb067AlphaDummy004 x y f) from (by
                  unfold nb067AlphaDummy004;
                  with_reducible
                    exact
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0043 x y f) 0))))
              (TAlphaVar.here _ _ _)))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0083`. -/
@[expose]
noncomputable def nb067SplitAlpha0083 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy341), (nb067AlphaDummy344 f)),
        ((nb067AlphaDummy340), (nb067AlphaDummy343 f)),
        ((nb067AlphaDummy339), (nb067AlphaDummy342 f)),
        ((nb067AlphaDummy337), (nb067AlphaDummy338 f)),
        ((nb067AlphaDummy333), (nb067AlphaDummy335 f)),
        ((nb067AlphaDummy334), (nb067AlphaDummy336 f)),
        ((nb067AlphaDummy326), (nb067AlphaDummy328 f)),
        ((nb067AlphaDummy325), (nb067AlphaDummy327 f)),
        ((nb067AlphaDummy331), (nb067AlphaDummy332 f)),
        ((nb067AlphaDummy329), (nb067AlphaDummy330 f)),
        ((nb067AlphaDummy322), (nb067AlphaDummy324 f)),
        ((nb067AlphaDummy321), (nb067AlphaDummy323 f)),
        ((nb067AlphaDummy319), (nb067AlphaDummy320 x f)),
        ((nb067AlphaDummy317), (nb067AlphaDummy318 x f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb067AlphaDummy340)) (Class.cv (nb067AlphaDummy341)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb067AlphaDummy339))
            (synCun (Class.cv (nb067AlphaDummy340)) (Class.cv (nb067AlphaDummy341))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb067AlphaDummy343 f))
            (Class.cv (nb067AlphaDummy344 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy342 f))
            (synCun (Class.cv (nb067AlphaDummy343 f))
              (Class.cv (nb067AlphaDummy344 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy340) ≠ (nb067AlphaDummy347) from (by
                              unfold nb067AlphaDummy347;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0356) 0))))
                          (show (nb067AlphaDummy343 f) ≠ (nb067AlphaDummy348 f) from (by
                              unfold nb067AlphaDummy348;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0357 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy340) ≠ (nb067AlphaDummy345) from (by
                                unfold nb067AlphaDummy345;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0354) 0))))
                            (show (nb067AlphaDummy343 f) ≠ (nb067AlphaDummy346 f) from (by
                                unfold nb067AlphaDummy346;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0355 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy333))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy335 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy341) ≠ (nb067AlphaDummy347) from (by
                              unfold nb067AlphaDummy347;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0360) 0))))
                          (show (nb067AlphaDummy344 f) ≠ (nb067AlphaDummy348 f) from (by
                              unfold nb067AlphaDummy348;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0361 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy341) ≠ (nb067AlphaDummy345) from (by
                                unfold nb067AlphaDummy345;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0358) 0))))
                            (show (nb067AlphaDummy344 f) ≠ (nb067AlphaDummy346 f) from (by
                                unfold nb067AlphaDummy346;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0359 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy340) ≠ (nb067AlphaDummy347) from (by
                              unfold nb067AlphaDummy347;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0356) 0))))
                          (show (nb067AlphaDummy343 f) ≠ (nb067AlphaDummy348 f) from (by
                              unfold nb067AlphaDummy348;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0357 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy340) ≠ (nb067AlphaDummy345) from (by
                                unfold nb067AlphaDummy345;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0354) 0))))
                            (show (nb067AlphaDummy343 f) ≠ (nb067AlphaDummy346 f) from (by
                                unfold nb067AlphaDummy346;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0355 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy333))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy335 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy341) ≠ (nb067AlphaDummy347) from (by
                              unfold nb067AlphaDummy347;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0360) 0))))
                          (show (nb067AlphaDummy344 f) ≠ (nb067AlphaDummy348 f) from (by
                              unfold nb067AlphaDummy348;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0361 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy341) ≠ (nb067AlphaDummy345) from (by
                                unfold nb067AlphaDummy345;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0358) 0))))
                            (show (nb067AlphaDummy344 f) ≠ (nb067AlphaDummy346 f) from (by
                                unfold nb067AlphaDummy346;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0359 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb067AlphaDummy341), (nb067AlphaDummy344 f)),
          ((nb067AlphaDummy340), (nb067AlphaDummy343 f)),
          ((nb067AlphaDummy339), (nb067AlphaDummy342 f)),
          ((nb067AlphaDummy337), (nb067AlphaDummy338 f)),
          ((nb067AlphaDummy333), (nb067AlphaDummy335 f)),
          ((nb067AlphaDummy334), (nb067AlphaDummy336 f)),
          ((nb067AlphaDummy326), (nb067AlphaDummy328 f)),
          ((nb067AlphaDummy325), (nb067AlphaDummy327 f)),
          ((nb067AlphaDummy331), (nb067AlphaDummy332 f)),
          ((nb067AlphaDummy329), (nb067AlphaDummy330 f)),
          ((nb067AlphaDummy322), (nb067AlphaDummy324 f)),
          ((nb067AlphaDummy321), (nb067AlphaDummy323 f)),
          ((nb067AlphaDummy319), (nb067AlphaDummy320 x f)),
          ((nb067AlphaDummy317), (nb067AlphaDummy318 x f)), ((nb067AlphaDummy000), f),
          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy333))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067AlphaDummy335 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067AlphaDummy333))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067AlphaDummy335 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy340) ≠ (nb067AlphaDummy351) from (by
                                unfold nb067AlphaDummy351;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0364) 0))))
                            (show (nb067AlphaDummy343 f) ≠ (nb067AlphaDummy352 f) from (by
                                unfold nb067AlphaDummy352;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0365 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy340) ≠ (nb067AlphaDummy349) from (by
                                  unfold nb067AlphaDummy349;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0362) 0))))
                              (show (nb067AlphaDummy343 f) ≠ (nb067AlphaDummy350 f) from
                                (by
                                  unfold nb067AlphaDummy350;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0363 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy333))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy335 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy340) ≠ (nb067AlphaDummy351) from (by
                                unfold nb067AlphaDummy351;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0364) 0))))
                            (show (nb067AlphaDummy343 f) ≠ (nb067AlphaDummy352 f) from (by
                                unfold nb067AlphaDummy352;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0365 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy340) ≠ (nb067AlphaDummy349) from (by
                                  unfold nb067AlphaDummy349;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0362) 0))))
                              (show (nb067AlphaDummy343 f) ≠ (nb067AlphaDummy350 f) from
                                (by
                                  unfold nb067AlphaDummy350;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0363 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy333))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy335 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy341) ≠ (nb067AlphaDummy353) from (by
                                unfold nb067AlphaDummy353;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0368) 0))))
                            (show (nb067AlphaDummy344 f) ≠ (nb067AlphaDummy354 f) from (by
                                unfold nb067AlphaDummy354;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0369 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy341) ≠ (nb067AlphaDummy349) from (by
                                  unfold nb067AlphaDummy349;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0366) 0))))
                              (show (nb067AlphaDummy344 f) ≠ (nb067AlphaDummy350 f) from
                                (by
                                  unfold nb067AlphaDummy350;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0367 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy341) ≠ (nb067AlphaDummy353) from (by
                                unfold nb067AlphaDummy353;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0368) 0))))
                            (show (nb067AlphaDummy344 f) ≠ (nb067AlphaDummy354 f) from (by
                                unfold nb067AlphaDummy354;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0369 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy341) ≠ (nb067AlphaDummy349) from (by
                                  unfold nb067AlphaDummy349;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0366) 0))))
                              (show (nb067AlphaDummy344 f) ≠ (nb067AlphaDummy350 f) from
                                (by
                                  unfold nb067AlphaDummy350;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0367 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0084`. -/
@[expose]
noncomputable def nb067SplitAlpha0084 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy333), (nb067AlphaDummy335 f)),
        ((nb067AlphaDummy334), (nb067AlphaDummy336 f)),
        ((nb067AlphaDummy326), (nb067AlphaDummy328 f)),
        ((nb067AlphaDummy325), (nb067AlphaDummy327 f)),
        ((nb067AlphaDummy331), (nb067AlphaDummy332 f)),
        ((nb067AlphaDummy329), (nb067AlphaDummy330 f)),
        ((nb067AlphaDummy322), (nb067AlphaDummy324 f)),
        ((nb067AlphaDummy321), (nb067AlphaDummy323 f)),
        ((nb067AlphaDummy319), (nb067AlphaDummy320 x f)),
        ((nb067AlphaDummy317), (nb067AlphaDummy318 x f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.neg (synWa (Wff.classMem (Class.cv (nb067AlphaDummy333))
            (Class.cv (nb067AlphaDummy326))) (Wff.classEq (Class.cv (nb067AlphaDummy334))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy333)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy333)) (synC1c))
              (Class.cv (nb067AlphaDummy333))))))
      (Wff.neg (synWa (Wff.classMem (Class.cv (nb067AlphaDummy335 f))
            (Class.cv (nb067AlphaDummy328 f)))
          (Wff.classEq (Class.cv (nb067AlphaDummy336 f))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy335 f)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy335 f)) (synC1c))
              (Class.cv (nb067AlphaDummy335 f)))))) :=
  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there
            (show (nb067AlphaDummy326) ≠ (nb067AlphaDummy333) from (by
                unfold nb067AlphaDummy333;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0348) 0))))
            (show (nb067AlphaDummy328 f) ≠ (nb067AlphaDummy335 f) from (by
                unfold nb067AlphaDummy335;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0349 f) 0))))
            (TAlphaVar.there (show (nb067AlphaDummy326) ≠ (nb067AlphaDummy334) from (by
                  unfold nb067AlphaDummy334;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0348) 1))))
              (show (nb067AlphaDummy328 f) ≠ (nb067AlphaDummy336 f) from (by
                  unfold nb067AlphaDummy336;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0349 f) 1))))
              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy326))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb067AlphaDummy328 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb067AlphaDummy333) ≠ (nb067AlphaDummy340) from (by
                                  unfold nb067AlphaDummy340;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0352) 1))))
                              (show (nb067AlphaDummy335 f) ≠ (nb067AlphaDummy343 f) from
                                (by
                                  unfold nb067AlphaDummy343;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0353 f) 1))))
                              (TAlphaVar.there
                                (show (nb067AlphaDummy333) ≠ (nb067AlphaDummy339) from (by
                                    unfold nb067AlphaDummy339;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0352) 0)))) (show
                                  (nb067AlphaDummy335 f) ≠ (nb067AlphaDummy342 f) from (by
                                    unfold nb067AlphaDummy342;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0353 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb067AlphaDummy333) ≠ (nb067AlphaDummy337) from
                                    (by
                                      unfold nb067AlphaDummy337;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0350)
                                              0)))) (show
                                    (nb067AlphaDummy335 f) ≠ (nb067AlphaDummy338 f) from
                                    (by
                                      unfold nb067AlphaDummy338;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0351 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb067AlphaDummy341), (nb067AlphaDummy344 f)),
                                  ((nb067AlphaDummy340), (nb067AlphaDummy343 f)),
                                  ((nb067AlphaDummy339), (nb067AlphaDummy342 f)),
                                  ((nb067AlphaDummy337), (nb067AlphaDummy338 f)),
                                  ((nb067AlphaDummy333), (nb067AlphaDummy335 f)),
                                  ((nb067AlphaDummy334), (nb067AlphaDummy336 f)),
                                  ((nb067AlphaDummy326), (nb067AlphaDummy328 f)),
                                  ((nb067AlphaDummy325), (nb067AlphaDummy327 f)),
                                  ((nb067AlphaDummy331), (nb067AlphaDummy332 f)),
                                  ((nb067AlphaDummy329), (nb067AlphaDummy330 f)),
                                  ((nb067AlphaDummy322), (nb067AlphaDummy324 f)),
                                  ((nb067AlphaDummy321), (nb067AlphaDummy323 f)),
                                  ((nb067AlphaDummy319), (nb067AlphaDummy320 x f)),
                                  ((nb067AlphaDummy317), (nb067AlphaDummy318 x f)),
                                  ((nb067AlphaDummy000), f), ((nb067AlphaDummy003),
                                    (nb067AlphaDummy004 x y f)),
                                  ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                                  ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb067SplitAlpha0083 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb067AlphaDummy333) ≠ (nb067AlphaDummy337) from (by
                          unfold nb067AlphaDummy337;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0350) 0))))
                      (show (nb067AlphaDummy335 f) ≠ (nb067AlphaDummy338 f) from (by
                          unfold nb067AlphaDummy338;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0351 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb067AlphaDummy337), (nb067AlphaDummy338 f)),
                      ((nb067AlphaDummy333), (nb067AlphaDummy335 f)),
                      ((nb067AlphaDummy334), (nb067AlphaDummy336 f)),
                      ((nb067AlphaDummy326), (nb067AlphaDummy328 f)),
                      ((nb067AlphaDummy325), (nb067AlphaDummy327 f)),
                      ((nb067AlphaDummy331), (nb067AlphaDummy332 f)),
                      ((nb067AlphaDummy329), (nb067AlphaDummy330 f)),
                      ((nb067AlphaDummy322), (nb067AlphaDummy324 f)),
                      ((nb067AlphaDummy321), (nb067AlphaDummy323 f)),
                      ((nb067AlphaDummy319), (nb067AlphaDummy320 x f)),
                      ((nb067AlphaDummy317), (nb067AlphaDummy318 x f)),
                      ((nb067AlphaDummy000), f),
                      ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                      ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                      ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067AlphaDummy333) ≠ (nb067AlphaDummy337) from
                      (by
                        unfold nb067AlphaDummy337;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0350) 0))))
                    (show (nb067AlphaDummy335 f) ≠ (nb067AlphaDummy338 f) from (by
                        unfold nb067AlphaDummy338;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0351 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb067AlphaDummy333) ≠ (nb067AlphaDummy337) from (by
                          unfold nb067AlphaDummy337;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0350) 0))))
                      (show (nb067AlphaDummy335 f) ≠ (nb067AlphaDummy338 f) from (by
                          unfold nb067AlphaDummy338;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0351 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb067AlphaDummy337), (nb067AlphaDummy338 f)),
                      ((nb067AlphaDummy333), (nb067AlphaDummy335 f)),
                      ((nb067AlphaDummy334), (nb067AlphaDummy336 f)),
                      ((nb067AlphaDummy326), (nb067AlphaDummy328 f)),
                      ((nb067AlphaDummy325), (nb067AlphaDummy327 f)),
                      ((nb067AlphaDummy331), (nb067AlphaDummy332 f)),
                      ((nb067AlphaDummy329), (nb067AlphaDummy330 f)),
                      ((nb067AlphaDummy322), (nb067AlphaDummy324 f)),
                      ((nb067AlphaDummy321), (nb067AlphaDummy323 f)),
                      ((nb067AlphaDummy319), (nb067AlphaDummy320 x f)),
                      ((nb067AlphaDummy317), (nb067AlphaDummy318 x f)),
                      ((nb067AlphaDummy000), f),
                      ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                      ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                      ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part033`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0085`. -/
@[expose]
noncomputable def nb067SplitAlpha0085 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy341), (nb067AlphaDummy344 f)),
        ((nb067AlphaDummy340), (nb067AlphaDummy343 f)),
        ((nb067AlphaDummy339), (nb067AlphaDummy342 f)),
        ((nb067AlphaDummy337), (nb067AlphaDummy338 f)),
        ((nb067AlphaDummy333), (nb067AlphaDummy335 f)),
        ((nb067AlphaDummy334), (nb067AlphaDummy336 f)),
        ((nb067AlphaDummy359), (nb067AlphaDummy360 f)),
        ((nb067AlphaDummy357), (nb067AlphaDummy358 f)),
        ((nb067AlphaDummy326), (nb067AlphaDummy328 f)),
        ((nb067AlphaDummy325), (nb067AlphaDummy327 f)),
        ((nb067AlphaDummy355), (nb067AlphaDummy356 f)),
        ((nb067AlphaDummy329), (nb067AlphaDummy330 f)),
        ((nb067AlphaDummy322), (nb067AlphaDummy324 f)),
        ((nb067AlphaDummy321), (nb067AlphaDummy323 f)),
        ((nb067AlphaDummy319), (nb067AlphaDummy320 x f)),
        ((nb067AlphaDummy317), (nb067AlphaDummy318 x f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb067AlphaDummy340)) (Class.cv (nb067AlphaDummy341)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb067AlphaDummy339))
            (synCun (Class.cv (nb067AlphaDummy340)) (Class.cv (nb067AlphaDummy341))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb067AlphaDummy343 f))
            (Class.cv (nb067AlphaDummy344 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy342 f))
            (synCun (Class.cv (nb067AlphaDummy343 f))
              (Class.cv (nb067AlphaDummy344 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy340) ≠ (nb067AlphaDummy347) from (by
                              unfold nb067AlphaDummy347;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0356) 0))))
                          (show (nb067AlphaDummy343 f) ≠ (nb067AlphaDummy348 f) from (by
                              unfold nb067AlphaDummy348;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0357 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy340) ≠ (nb067AlphaDummy345) from (by
                                unfold nb067AlphaDummy345;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0354) 0))))
                            (show (nb067AlphaDummy343 f) ≠ (nb067AlphaDummy346 f) from (by
                                unfold nb067AlphaDummy346;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0355 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy333))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy335 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy341) ≠ (nb067AlphaDummy347) from (by
                              unfold nb067AlphaDummy347;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0360) 0))))
                          (show (nb067AlphaDummy344 f) ≠ (nb067AlphaDummy348 f) from (by
                              unfold nb067AlphaDummy348;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0361 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy341) ≠ (nb067AlphaDummy345) from (by
                                unfold nb067AlphaDummy345;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0358) 0))))
                            (show (nb067AlphaDummy344 f) ≠ (nb067AlphaDummy346 f) from (by
                                unfold nb067AlphaDummy346;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0359 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy340) ≠ (nb067AlphaDummy347) from (by
                              unfold nb067AlphaDummy347;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0356) 0))))
                          (show (nb067AlphaDummy343 f) ≠ (nb067AlphaDummy348 f) from (by
                              unfold nb067AlphaDummy348;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0357 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy340) ≠ (nb067AlphaDummy345) from (by
                                unfold nb067AlphaDummy345;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0354) 0))))
                            (show (nb067AlphaDummy343 f) ≠ (nb067AlphaDummy346 f) from (by
                                unfold nb067AlphaDummy346;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0355 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy333))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy335 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy341) ≠ (nb067AlphaDummy347) from (by
                              unfold nb067AlphaDummy347;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0360) 0))))
                          (show (nb067AlphaDummy344 f) ≠ (nb067AlphaDummy348 f) from (by
                              unfold nb067AlphaDummy348;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0361 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy341) ≠ (nb067AlphaDummy345) from (by
                                unfold nb067AlphaDummy345;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0358) 0))))
                            (show (nb067AlphaDummy344 f) ≠ (nb067AlphaDummy346 f) from (by
                                unfold nb067AlphaDummy346;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0359 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb067AlphaDummy341), (nb067AlphaDummy344 f)),
          ((nb067AlphaDummy340), (nb067AlphaDummy343 f)),
          ((nb067AlphaDummy339), (nb067AlphaDummy342 f)),
          ((nb067AlphaDummy337), (nb067AlphaDummy338 f)),
          ((nb067AlphaDummy333), (nb067AlphaDummy335 f)),
          ((nb067AlphaDummy334), (nb067AlphaDummy336 f)),
          ((nb067AlphaDummy359), (nb067AlphaDummy360 f)),
          ((nb067AlphaDummy357), (nb067AlphaDummy358 f)),
          ((nb067AlphaDummy326), (nb067AlphaDummy328 f)),
          ((nb067AlphaDummy325), (nb067AlphaDummy327 f)),
          ((nb067AlphaDummy355), (nb067AlphaDummy356 f)),
          ((nb067AlphaDummy329), (nb067AlphaDummy330 f)),
          ((nb067AlphaDummy322), (nb067AlphaDummy324 f)),
          ((nb067AlphaDummy321), (nb067AlphaDummy323 f)),
          ((nb067AlphaDummy319), (nb067AlphaDummy320 x f)),
          ((nb067AlphaDummy317), (nb067AlphaDummy318 x f)), ((nb067AlphaDummy000), f),
          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy333))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067AlphaDummy335 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067AlphaDummy333))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067AlphaDummy335 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy340) ≠ (nb067AlphaDummy351) from (by
                                unfold nb067AlphaDummy351;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0364) 0))))
                            (show (nb067AlphaDummy343 f) ≠ (nb067AlphaDummy352 f) from (by
                                unfold nb067AlphaDummy352;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0365 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy340) ≠ (nb067AlphaDummy349) from (by
                                  unfold nb067AlphaDummy349;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0362) 0))))
                              (show (nb067AlphaDummy343 f) ≠ (nb067AlphaDummy350 f) from
                                (by
                                  unfold nb067AlphaDummy350;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0363 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy333))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy335 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy340) ≠ (nb067AlphaDummy351) from (by
                                unfold nb067AlphaDummy351;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0364) 0))))
                            (show (nb067AlphaDummy343 f) ≠ (nb067AlphaDummy352 f) from (by
                                unfold nb067AlphaDummy352;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0365 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy340) ≠ (nb067AlphaDummy349) from (by
                                  unfold nb067AlphaDummy349;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0362) 0))))
                              (show (nb067AlphaDummy343 f) ≠ (nb067AlphaDummy350 f) from
                                (by
                                  unfold nb067AlphaDummy350;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0363 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy333))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy335 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy341) ≠ (nb067AlphaDummy353) from (by
                                unfold nb067AlphaDummy353;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0368) 0))))
                            (show (nb067AlphaDummy344 f) ≠ (nb067AlphaDummy354 f) from (by
                                unfold nb067AlphaDummy354;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0369 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy341) ≠ (nb067AlphaDummy349) from (by
                                  unfold nb067AlphaDummy349;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0366) 0))))
                              (show (nb067AlphaDummy344 f) ≠ (nb067AlphaDummy350 f) from
                                (by
                                  unfold nb067AlphaDummy350;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0367 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy341) ≠ (nb067AlphaDummy353) from (by
                                unfold nb067AlphaDummy353;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0368) 0))))
                            (show (nb067AlphaDummy344 f) ≠ (nb067AlphaDummy354 f) from (by
                                unfold nb067AlphaDummy354;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0369 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy341) ≠ (nb067AlphaDummy349) from (by
                                  unfold nb067AlphaDummy349;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0366) 0))))
                              (show (nb067AlphaDummy344 f) ≠ (nb067AlphaDummy350 f) from
                                (by
                                  unfold nb067AlphaDummy350;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0367 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0086`. -/
@[expose]
noncomputable def nb067SplitAlpha0086 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy333), (nb067AlphaDummy335 f)),
        ((nb067AlphaDummy334), (nb067AlphaDummy336 f)),
        ((nb067AlphaDummy359), (nb067AlphaDummy360 f)),
        ((nb067AlphaDummy357), (nb067AlphaDummy358 f)),
        ((nb067AlphaDummy326), (nb067AlphaDummy328 f)),
        ((nb067AlphaDummy325), (nb067AlphaDummy327 f)),
        ((nb067AlphaDummy355), (nb067AlphaDummy356 f)),
        ((nb067AlphaDummy329), (nb067AlphaDummy330 f)),
        ((nb067AlphaDummy322), (nb067AlphaDummy324 f)),
        ((nb067AlphaDummy321), (nb067AlphaDummy323 f)),
        ((nb067AlphaDummy319), (nb067AlphaDummy320 x f)),
        ((nb067AlphaDummy317), (nb067AlphaDummy318 x f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy333))
          (Class.cv (nb067AlphaDummy326))) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy334))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy333)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy333)) (synC1c))
              (Class.cv (nb067AlphaDummy333))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy335 f))
          (Class.cv (nb067AlphaDummy328 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy336 f))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy335 f)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy335 f)) (synC1c))
              (Class.cv (nb067AlphaDummy335 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067AlphaDummy326) ≠ (nb067AlphaDummy333) from (by
              unfold nb067AlphaDummy333;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0348) 0))))
          (show (nb067AlphaDummy328 f) ≠ (nb067AlphaDummy335 f) from (by
              unfold nb067AlphaDummy335;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0349 f) 0))))
          (TAlphaVar.there (show (nb067AlphaDummy326) ≠ (nb067AlphaDummy334) from (by
                unfold nb067AlphaDummy334;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0348) 1))))
            (show (nb067AlphaDummy328 f) ≠ (nb067AlphaDummy336 f) from (by
                unfold nb067AlphaDummy336;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0349 f) 1))))
            (TAlphaVar.there (show (nb067AlphaDummy326) ≠ (nb067AlphaDummy359) from (by
                  unfold nb067AlphaDummy359;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0378) 0))))
              (show (nb067AlphaDummy328 f) ≠ (nb067AlphaDummy360 f) from (by
                  unfold nb067AlphaDummy360;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0379 f) 0))))
              (TAlphaVar.there (show (nb067AlphaDummy326) ≠ (nb067AlphaDummy357) from (by
                    unfold nb067AlphaDummy357;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0376) 0))))
                (show (nb067AlphaDummy328 f) ≠ (nb067AlphaDummy358 f) from (by
                    unfold nb067AlphaDummy358;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0377 f) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy326))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb067AlphaDummy328 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb067AlphaDummy333) ≠ (nb067AlphaDummy340) from (by
                                  unfold nb067AlphaDummy340;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0352) 1))))
                              (show (nb067AlphaDummy335 f) ≠ (nb067AlphaDummy343 f) from
                                (by
                                  unfold nb067AlphaDummy343;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0353 f) 1))))
                              (TAlphaVar.there
                                (show (nb067AlphaDummy333) ≠ (nb067AlphaDummy339) from (by
                                    unfold nb067AlphaDummy339;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0352) 0)))) (show
                                  (nb067AlphaDummy335 f) ≠ (nb067AlphaDummy342 f) from (by
                                    unfold nb067AlphaDummy342;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0353 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb067AlphaDummy333) ≠ (nb067AlphaDummy337) from
                                    (by
                                      unfold nb067AlphaDummy337;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0350)
                                              0)))) (show
                                    (nb067AlphaDummy335 f) ≠ (nb067AlphaDummy338 f) from
                                    (by
                                      unfold nb067AlphaDummy338;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0351 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb067AlphaDummy341), (nb067AlphaDummy344 f)),
                                  ((nb067AlphaDummy340), (nb067AlphaDummy343 f)),
                                  ((nb067AlphaDummy339), (nb067AlphaDummy342 f)),
                                  ((nb067AlphaDummy337), (nb067AlphaDummy338 f)),
                                  ((nb067AlphaDummy333), (nb067AlphaDummy335 f)),
                                  ((nb067AlphaDummy334), (nb067AlphaDummy336 f)),
                                  ((nb067AlphaDummy359), (nb067AlphaDummy360 f)),
                                  ((nb067AlphaDummy357), (nb067AlphaDummy358 f)),
                                  ((nb067AlphaDummy326), (nb067AlphaDummy328 f)),
                                  ((nb067AlphaDummy325), (nb067AlphaDummy327 f)),
                                  ((nb067AlphaDummy355), (nb067AlphaDummy356 f)),
                                  ((nb067AlphaDummy329), (nb067AlphaDummy330 f)),
                                  ((nb067AlphaDummy322), (nb067AlphaDummy324 f)),
                                  ((nb067AlphaDummy321), (nb067AlphaDummy323 f)),
                                  ((nb067AlphaDummy319), (nb067AlphaDummy320 x f)),
                                  ((nb067AlphaDummy317), (nb067AlphaDummy318 x f)),
                                  ((nb067AlphaDummy000), f), ((nb067AlphaDummy003),
                                    (nb067AlphaDummy004 x y f)),
                                  ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                                  ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb067SplitAlpha0085 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb067AlphaDummy333) ≠ (nb067AlphaDummy337) from (by
                          unfold nb067AlphaDummy337;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0350) 0))))
                      (show (nb067AlphaDummy335 f) ≠ (nb067AlphaDummy338 f) from (by
                          unfold nb067AlphaDummy338;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0351 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb067AlphaDummy337), (nb067AlphaDummy338 f)),
                      ((nb067AlphaDummy333), (nb067AlphaDummy335 f)),
                      ((nb067AlphaDummy334), (nb067AlphaDummy336 f)),
                      ((nb067AlphaDummy359), (nb067AlphaDummy360 f)),
                      ((nb067AlphaDummy357), (nb067AlphaDummy358 f)),
                      ((nb067AlphaDummy326), (nb067AlphaDummy328 f)),
                      ((nb067AlphaDummy325), (nb067AlphaDummy327 f)),
                      ((nb067AlphaDummy355), (nb067AlphaDummy356 f)),
                      ((nb067AlphaDummy329), (nb067AlphaDummy330 f)),
                      ((nb067AlphaDummy322), (nb067AlphaDummy324 f)),
                      ((nb067AlphaDummy321), (nb067AlphaDummy323 f)),
                      ((nb067AlphaDummy319), (nb067AlphaDummy320 x f)),
                      ((nb067AlphaDummy317), (nb067AlphaDummy318 x f)),
                      ((nb067AlphaDummy000), f),
                      ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                      ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                      ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067AlphaDummy333) ≠ (nb067AlphaDummy337) from
                      (by
                        unfold nb067AlphaDummy337;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0350) 0))))
                    (show (nb067AlphaDummy335 f) ≠ (nb067AlphaDummy338 f) from (by
                        unfold nb067AlphaDummy338;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0351 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb067AlphaDummy333) ≠ (nb067AlphaDummy337) from (by
                          unfold nb067AlphaDummy337;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0350) 0))))
                      (show (nb067AlphaDummy335 f) ≠ (nb067AlphaDummy338 f) from (by
                          unfold nb067AlphaDummy338;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0351 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb067AlphaDummy337), (nb067AlphaDummy338 f)),
                      ((nb067AlphaDummy333), (nb067AlphaDummy335 f)),
                      ((nb067AlphaDummy334), (nb067AlphaDummy336 f)),
                      ((nb067AlphaDummy359), (nb067AlphaDummy360 f)),
                      ((nb067AlphaDummy357), (nb067AlphaDummy358 f)),
                      ((nb067AlphaDummy326), (nb067AlphaDummy328 f)),
                      ((nb067AlphaDummy325), (nb067AlphaDummy327 f)),
                      ((nb067AlphaDummy355), (nb067AlphaDummy356 f)),
                      ((nb067AlphaDummy329), (nb067AlphaDummy330 f)),
                      ((nb067AlphaDummy322), (nb067AlphaDummy324 f)),
                      ((nb067AlphaDummy321), (nb067AlphaDummy323 f)),
                      ((nb067AlphaDummy319), (nb067AlphaDummy320 x f)),
                      ((nb067AlphaDummy317), (nb067AlphaDummy318 x f)),
                      ((nb067AlphaDummy000), f),
                      ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                      ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                      ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0087`. -/
@[expose]
noncomputable def nb067SplitAlpha0087 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy355), (nb067AlphaDummy356 f)),
        ((nb067AlphaDummy329), (nb067AlphaDummy330 f)),
        ((nb067AlphaDummy322), (nb067AlphaDummy324 f)),
        ((nb067AlphaDummy321), (nb067AlphaDummy323 f)),
        ((nb067AlphaDummy319), (nb067AlphaDummy320 x f)),
        ((nb067AlphaDummy317), (nb067AlphaDummy318 x f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy355))
          (Class.cab (nb067AlphaDummy325)
            (synWrex (nb067AlphaDummy326) (Class.cv (nb067AlphaDummy321))
              (Wff.classEq (Class.cv (nb067AlphaDummy325))
                (synCun (synCphi (Class.cv (nb067AlphaDummy326))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb067AlphaDummy355))
            (Class.cab (nb067AlphaDummy325)
              (synWrex (nb067AlphaDummy326) (Class.cv (nb067AlphaDummy321))
                (Wff.classEq (Class.cv (nb067AlphaDummy325))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy326)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy356 f))
          (Class.cab (nb067AlphaDummy327 f)
            (synWrex (nb067AlphaDummy328 f) (Class.cv (nb067AlphaDummy323 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy327 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy328 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb067AlphaDummy356 f))
            (Class.cab (nb067AlphaDummy327 f)
              (synWrex (nb067AlphaDummy328 f) (Class.cv (nb067AlphaDummy323 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy327 f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy328 f)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb067AlphaDummy321) ≠ (nb067AlphaDummy326) from
                    (by
                      unfold nb067AlphaDummy326;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0370) 1))))
                  (show (nb067AlphaDummy323 f) ≠ (nb067AlphaDummy328 f) from (by
                      unfold nb067AlphaDummy328;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0372 f) 1))))
                  (TAlphaVar.there (show (nb067AlphaDummy321) ≠ (nb067AlphaDummy325) from
                      (by
                        unfold nb067AlphaDummy325;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0370) 0))))
                    (show (nb067AlphaDummy323 f) ≠ (nb067AlphaDummy327 f) from (by
                        unfold nb067AlphaDummy327;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0372 f) 0)))) (TAlphaVar.there
                      (show (nb067AlphaDummy321) ≠ (nb067AlphaDummy355) from (by
                          unfold nb067AlphaDummy355;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0374) 0))))
                      (show (nb067AlphaDummy323 f) ≠ (nb067AlphaDummy356 f) from (by
                          unfold nb067AlphaDummy356;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0375 f) 0))))
                      (TAlphaVar.there
                        (show (nb067AlphaDummy321) ≠ (nb067AlphaDummy329) from (by
                            unfold nb067AlphaDummy329;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0371) 0))))
                        (show (nb067AlphaDummy323 f) ≠ (nb067AlphaDummy330 f) from (by
                            unfold nb067AlphaDummy330;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0373 f) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb067AlphaDummy000))).fv ∪ ((synCvv)).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv f)).fv ∪ ((synCvv)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb067AlphaDummy322))).fv ∪
                      ((Class.cv (nb067AlphaDummy321))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb067AlphaDummy324 f))).fv ∪
                      ((Class.cv (nb067AlphaDummy323 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067SplitAlpha0086 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067SplitAlpha0086 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb067AlphaDummy357), (nb067AlphaDummy358 f)),
                          ((nb067AlphaDummy326), (nb067AlphaDummy328 f)),
                          ((nb067AlphaDummy325), (nb067AlphaDummy327 f)),
                          ((nb067AlphaDummy355), (nb067AlphaDummy356 f)),
                          ((nb067AlphaDummy329), (nb067AlphaDummy330 f)),
                          ((nb067AlphaDummy322), (nb067AlphaDummy324 f)),
                          ((nb067AlphaDummy321), (nb067AlphaDummy323 f)),
                          ((nb067AlphaDummy319), (nb067AlphaDummy320 x f)),
                          ((nb067AlphaDummy317), (nb067AlphaDummy318 x f)),
                          ((nb067AlphaDummy000), f),
                          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067AlphaDummy321) ≠ (nb067AlphaDummy326) from
                      (by
                        unfold nb067AlphaDummy326;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0370) 1))))
                    (show (nb067AlphaDummy323 f) ≠ (nb067AlphaDummy328 f) from (by
                        unfold nb067AlphaDummy328;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0372 f) 1)))) (TAlphaVar.there
                      (show (nb067AlphaDummy321) ≠ (nb067AlphaDummy325) from (by
                          unfold nb067AlphaDummy325;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0370) 0))))
                      (show (nb067AlphaDummy323 f) ≠ (nb067AlphaDummy327 f) from (by
                          unfold nb067AlphaDummy327;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0372 f) 0))))
                      (TAlphaVar.there
                        (show (nb067AlphaDummy321) ≠ (nb067AlphaDummy355) from (by
                            unfold nb067AlphaDummy355;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0374) 0))))
                        (show (nb067AlphaDummy323 f) ≠ (nb067AlphaDummy356 f) from (by
                            unfold nb067AlphaDummy356;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0375 f) 0))))
                        (TAlphaVar.there
                          (show (nb067AlphaDummy321) ≠ (nb067AlphaDummy329) from (by
                              unfold nb067AlphaDummy329;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0371) 0))))
                          (show (nb067AlphaDummy323 f) ≠ (nb067AlphaDummy330 f) from (by
                              unfold nb067AlphaDummy330;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0373 f) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb067AlphaDummy000))).fv ∪ ((synCvv)).fv)
                              (by decide))
                            (freshVar_injective (((Class.cv f)).fv ∪ ((synCvv)).fv)
                              (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb067AlphaDummy322))).fv ∪
                        ((Class.cv (nb067AlphaDummy321))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb067AlphaDummy324 f))).fv ∪
                        ((Class.cv (nb067AlphaDummy323 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067SplitAlpha0086 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067SplitAlpha0086 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb067AlphaDummy357), (nb067AlphaDummy358 f)),
                            ((nb067AlphaDummy326), (nb067AlphaDummy328 f)),
                            ((nb067AlphaDummy325), (nb067AlphaDummy327 f)),
                            ((nb067AlphaDummy355), (nb067AlphaDummy356 f)),
                            ((nb067AlphaDummy329), (nb067AlphaDummy330 f)),
                            ((nb067AlphaDummy322), (nb067AlphaDummy324 f)),
                            ((nb067AlphaDummy321), (nb067AlphaDummy323 f)),
                            ((nb067AlphaDummy319), (nb067AlphaDummy320 x f)),
                            ((nb067AlphaDummy317), (nb067AlphaDummy318 x f)),
                            ((nb067AlphaDummy000), f),
                            ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                            ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                            ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0088`. -/
@[expose]
noncomputable def nb067SplitAlpha0088 (x : Var) (y : Var) (f : Var) (dv_f_x : f ≠ x)
    (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb067AlphaDummy319), (nb067AlphaDummy320 x f)),
        ((nb067AlphaDummy317), (nb067AlphaDummy318 x f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy319))
          (synCrn (Class.cv (nb067AlphaDummy000)))) (Wff.neg
          (Wff.classMem (Class.cv (nb067AlphaDummy319)) (Class.cv (nb067AlphaDummy001)))))
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy320 x f)) (synCrn (Class.cv f)))
        (Wff.neg (Wff.classMem (Class.cv (nb067AlphaDummy320 x f)) (Class.cv x)))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.reflOfClosed [((nb067AlphaDummy322), (nb067AlphaDummy324 f)),
                  ((nb067AlphaDummy321), (nb067AlphaDummy323 f)),
                  ((nb067AlphaDummy319), (nb067AlphaDummy320 x f)),
                  ((nb067AlphaDummy317), (nb067AlphaDummy318 x f)),
                  ((nb067AlphaDummy000), f),
                  ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                  ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                  ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                (synCvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb067AlphaDummy322) ≠
        (nb067AlphaDummy326) from (by
          unfold nb067AlphaDummy326;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0342) 1)))) (show (nb067AlphaDummy324 f) ≠
        (nb067AlphaDummy328 f) from (by
          unfold nb067AlphaDummy328;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0344 f) 1)))) (TAlphaVar.there (show
        (nb067AlphaDummy322) ≠ (nb067AlphaDummy325) from (by
          unfold nb067AlphaDummy325;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0342) 0)))) (show (nb067AlphaDummy324 f) ≠
        (nb067AlphaDummy327 f) from (by
          unfold nb067AlphaDummy327;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0344 f) 0)))) (TAlphaVar.there (show
        (nb067AlphaDummy322) ≠ (nb067AlphaDummy331) from (by
          unfold nb067AlphaDummy331;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0346) 0)))) (show (nb067AlphaDummy324 f) ≠
        (nb067AlphaDummy332 f) from (by
          unfold nb067AlphaDummy332;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0347 f) 0)))) (TAlphaVar.there (show
        (nb067AlphaDummy322) ≠ (nb067AlphaDummy329) from (by
          unfold nb067AlphaDummy329;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0343) 0)))) (show (nb067AlphaDummy324 f) ≠
        (nb067AlphaDummy330 f) from (by
          unfold nb067AlphaDummy330;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0345 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb067AlphaDummy322))).fv ∪ ((Class.cv (nb067AlphaDummy321))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb067AlphaDummy324 f))).fv ∪
        ((Class.cv (nb067AlphaDummy323 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all
        (nb067SplitAlpha0084 x y f)))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb067AlphaDummy322) ≠
        (nb067AlphaDummy326) from (by
          unfold nb067AlphaDummy326;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0342) 1)))) (show (nb067AlphaDummy324 f) ≠
        (nb067AlphaDummy328 f) from (by
          unfold nb067AlphaDummy328;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0344 f) 1)))) (TAlphaVar.there (show
        (nb067AlphaDummy322) ≠ (nb067AlphaDummy325) from (by
          unfold nb067AlphaDummy325;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0342) 0)))) (show (nb067AlphaDummy324 f) ≠
        (nb067AlphaDummy327 f) from (by
          unfold nb067AlphaDummy327;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0344 f) 0)))) (TAlphaVar.there (show
        (nb067AlphaDummy322) ≠ (nb067AlphaDummy331) from (by
          unfold nb067AlphaDummy331;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0346) 0)))) (show (nb067AlphaDummy324 f) ≠
        (nb067AlphaDummy332 f) from (by
          unfold nb067AlphaDummy332;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0347 f) 0)))) (TAlphaVar.there (show
        (nb067AlphaDummy322) ≠ (nb067AlphaDummy329) from (by
          unfold nb067AlphaDummy329;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0343) 0)))) (show (nb067AlphaDummy324 f) ≠
        (nb067AlphaDummy330 f) from (by
          unfold nb067AlphaDummy330;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0345 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb067AlphaDummy322))).fv ∪ ((Class.cv (nb067AlphaDummy321))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb067AlphaDummy324 f))).fv ∪
        ((Class.cv (nb067AlphaDummy323 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all
        (nb067SplitAlpha0084 x y f)))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.neg (nb067SplitAlpha0087 x y f))))))))
              (TAlphaClass.cv (TAlphaVar.there
                  (show (nb067AlphaDummy000) ≠ (nb067AlphaDummy322) from (by
                      unfold nb067AlphaDummy322;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0384) 1))))
                  (show f ≠ (nb067AlphaDummy324 f) from (by
                      unfold nb067AlphaDummy324;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0385 f) 1))))
                  (TAlphaVar.there (show (nb067AlphaDummy000) ≠ (nb067AlphaDummy321) from
                      (by
                        unfold nb067AlphaDummy321;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0384) 0))))
                    (show f ≠ (nb067AlphaDummy323 f) from (by
                        unfold nb067AlphaDummy323;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0385 f) 0)))) (TAlphaVar.there
                      (show (nb067AlphaDummy000) ≠ (nb067AlphaDummy319) from (by
                          unfold nb067AlphaDummy319;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0382) 0))))
                      (show f ≠ (nb067AlphaDummy320 x f) from (by
                          unfold nb067AlphaDummy320;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0383 x f) 0))))
                      (TAlphaVar.there
                        (show (nb067AlphaDummy000) ≠ (nb067AlphaDummy317) from (by
                            unfold nb067AlphaDummy317;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0380) 0))))
                        (show f ≠ (nb067AlphaDummy318 x f) from (by
                            unfold nb067AlphaDummy318;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0381 x f) 0))))
                        (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
          (TAlphaVar.there (show (nb067AlphaDummy001) ≠ (nb067AlphaDummy319) from (by
                unfold nb067AlphaDummy319;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0388) 0))))
            (show x ≠ (nb067AlphaDummy320 x f) from (by
                unfold nb067AlphaDummy320;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0389 x f) 0))))
            (TAlphaVar.there (show (nb067AlphaDummy001) ≠ (nb067AlphaDummy317) from (by
                  unfold nb067AlphaDummy317;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0386) 0))))
              (show x ≠ (nb067AlphaDummy318 x f) from (by
                  unfold nb067AlphaDummy318;
                  with_reducible
                    exact
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0387 x f) 0))))
              (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                (Ne.symm dv_f_x) (TAlphaVar.there
                  (show (nb067AlphaDummy001) ≠ (nb067AlphaDummy003) from (by
                      unfold nb067AlphaDummy003;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0006) 0))))
                  (show x ≠ (nb067AlphaDummy004 x y f) from (by
                      unfold nb067AlphaDummy004;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb067_support_mem_0007 x y f) 0))))
                  (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                    dv_x_y (TAlphaVar.here _ _ _))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part034`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0089`. -/
@[expose]
noncomputable def nb067SplitAlpha0089 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy341), (nb067AlphaDummy344 f)),
        ((nb067AlphaDummy340), (nb067AlphaDummy343 f)),
        ((nb067AlphaDummy339), (nb067AlphaDummy342 f)),
        ((nb067AlphaDummy337), (nb067AlphaDummy338 f)),
        ((nb067AlphaDummy333), (nb067AlphaDummy335 f)),
        ((nb067AlphaDummy334), (nb067AlphaDummy336 f)),
        ((nb067AlphaDummy326), (nb067AlphaDummy328 f)),
        ((nb067AlphaDummy325), (nb067AlphaDummy327 f)),
        ((nb067AlphaDummy331), (nb067AlphaDummy332 f)),
        ((nb067AlphaDummy329), (nb067AlphaDummy330 f)),
        ((nb067AlphaDummy322), (nb067AlphaDummy324 f)),
        ((nb067AlphaDummy321), (nb067AlphaDummy323 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb067AlphaDummy340)) (Class.cv (nb067AlphaDummy341)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb067AlphaDummy339))
            (synCun (Class.cv (nb067AlphaDummy340)) (Class.cv (nb067AlphaDummy341))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb067AlphaDummy343 f))
            (Class.cv (nb067AlphaDummy344 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy342 f))
            (synCun (Class.cv (nb067AlphaDummy343 f))
              (Class.cv (nb067AlphaDummy344 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy340) ≠ (nb067AlphaDummy347) from (by
                              unfold nb067AlphaDummy347;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0356) 0))))
                          (show (nb067AlphaDummy343 f) ≠ (nb067AlphaDummy348 f) from (by
                              unfold nb067AlphaDummy348;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0357 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy340) ≠ (nb067AlphaDummy345) from (by
                                unfold nb067AlphaDummy345;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0354) 0))))
                            (show (nb067AlphaDummy343 f) ≠ (nb067AlphaDummy346 f) from (by
                                unfold nb067AlphaDummy346;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0355 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy333))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy335 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy341) ≠ (nb067AlphaDummy347) from (by
                              unfold nb067AlphaDummy347;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0360) 0))))
                          (show (nb067AlphaDummy344 f) ≠ (nb067AlphaDummy348 f) from (by
                              unfold nb067AlphaDummy348;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0361 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy341) ≠ (nb067AlphaDummy345) from (by
                                unfold nb067AlphaDummy345;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0358) 0))))
                            (show (nb067AlphaDummy344 f) ≠ (nb067AlphaDummy346 f) from (by
                                unfold nb067AlphaDummy346;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0359 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy340) ≠ (nb067AlphaDummy347) from (by
                              unfold nb067AlphaDummy347;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0356) 0))))
                          (show (nb067AlphaDummy343 f) ≠ (nb067AlphaDummy348 f) from (by
                              unfold nb067AlphaDummy348;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0357 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy340) ≠ (nb067AlphaDummy345) from (by
                                unfold nb067AlphaDummy345;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0354) 0))))
                            (show (nb067AlphaDummy343 f) ≠ (nb067AlphaDummy346 f) from (by
                                unfold nb067AlphaDummy346;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0355 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy333))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy335 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy341) ≠ (nb067AlphaDummy347) from (by
                              unfold nb067AlphaDummy347;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0360) 0))))
                          (show (nb067AlphaDummy344 f) ≠ (nb067AlphaDummy348 f) from (by
                              unfold nb067AlphaDummy348;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0361 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy341) ≠ (nb067AlphaDummy345) from (by
                                unfold nb067AlphaDummy345;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0358) 0))))
                            (show (nb067AlphaDummy344 f) ≠ (nb067AlphaDummy346 f) from (by
                                unfold nb067AlphaDummy346;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0359 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb067AlphaDummy341), (nb067AlphaDummy344 f)),
          ((nb067AlphaDummy340), (nb067AlphaDummy343 f)),
          ((nb067AlphaDummy339), (nb067AlphaDummy342 f)),
          ((nb067AlphaDummy337), (nb067AlphaDummy338 f)),
          ((nb067AlphaDummy333), (nb067AlphaDummy335 f)),
          ((nb067AlphaDummy334), (nb067AlphaDummy336 f)),
          ((nb067AlphaDummy326), (nb067AlphaDummy328 f)),
          ((nb067AlphaDummy325), (nb067AlphaDummy327 f)),
          ((nb067AlphaDummy331), (nb067AlphaDummy332 f)),
          ((nb067AlphaDummy329), (nb067AlphaDummy330 f)),
          ((nb067AlphaDummy322), (nb067AlphaDummy324 f)),
          ((nb067AlphaDummy321), (nb067AlphaDummy323 f)), ((nb067AlphaDummy000), f),
          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy333))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067AlphaDummy335 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067AlphaDummy333))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067AlphaDummy335 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy340) ≠ (nb067AlphaDummy351) from (by
                                unfold nb067AlphaDummy351;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0364) 0))))
                            (show (nb067AlphaDummy343 f) ≠ (nb067AlphaDummy352 f) from (by
                                unfold nb067AlphaDummy352;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0365 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy340) ≠ (nb067AlphaDummy349) from (by
                                  unfold nb067AlphaDummy349;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0362) 0))))
                              (show (nb067AlphaDummy343 f) ≠ (nb067AlphaDummy350 f) from
                                (by
                                  unfold nb067AlphaDummy350;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0363 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy333))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy335 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy340) ≠ (nb067AlphaDummy351) from (by
                                unfold nb067AlphaDummy351;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0364) 0))))
                            (show (nb067AlphaDummy343 f) ≠ (nb067AlphaDummy352 f) from (by
                                unfold nb067AlphaDummy352;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0365 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy340) ≠ (nb067AlphaDummy349) from (by
                                  unfold nb067AlphaDummy349;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0362) 0))))
                              (show (nb067AlphaDummy343 f) ≠ (nb067AlphaDummy350 f) from
                                (by
                                  unfold nb067AlphaDummy350;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0363 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy333))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy335 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy341) ≠ (nb067AlphaDummy353) from (by
                                unfold nb067AlphaDummy353;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0368) 0))))
                            (show (nb067AlphaDummy344 f) ≠ (nb067AlphaDummy354 f) from (by
                                unfold nb067AlphaDummy354;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0369 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy341) ≠ (nb067AlphaDummy349) from (by
                                  unfold nb067AlphaDummy349;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0366) 0))))
                              (show (nb067AlphaDummy344 f) ≠ (nb067AlphaDummy350 f) from
                                (by
                                  unfold nb067AlphaDummy350;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0367 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy341) ≠ (nb067AlphaDummy353) from (by
                                unfold nb067AlphaDummy353;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0368) 0))))
                            (show (nb067AlphaDummy344 f) ≠ (nb067AlphaDummy354 f) from (by
                                unfold nb067AlphaDummy354;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0369 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy341) ≠ (nb067AlphaDummy349) from (by
                                  unfold nb067AlphaDummy349;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0366) 0))))
                              (show (nb067AlphaDummy344 f) ≠ (nb067AlphaDummy350 f) from
                                (by
                                  unfold nb067AlphaDummy350;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0367 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0090`. -/
@[expose]
noncomputable def nb067SplitAlpha0090 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy326), (nb067AlphaDummy328 f)),
        ((nb067AlphaDummy325), (nb067AlphaDummy327 f)),
        ((nb067AlphaDummy331), (nb067AlphaDummy332 f)),
        ((nb067AlphaDummy329), (nb067AlphaDummy330 f)),
        ((nb067AlphaDummy322), (nb067AlphaDummy324 f)),
        ((nb067AlphaDummy321), (nb067AlphaDummy323 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.classEq (Class.cv (nb067AlphaDummy325))
        (synCphi (Class.cv (nb067AlphaDummy326))))
      (Wff.classEq (Class.cv (nb067AlphaDummy327 f))
        (synCphi (Class.cv (nb067AlphaDummy328 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb067AlphaDummy322))).fv ∪ ((Class.cv (nb067AlphaDummy321))).fv)
          (by decide)) (freshVar_injective (((Class.cv (nb067AlphaDummy324 f))).fv ∪
            ((Class.cv (nb067AlphaDummy323 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (show (nb067AlphaDummy326) ≠ (nb067AlphaDummy333) from (by
                    unfold nb067AlphaDummy333;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0348) 0))))
                (show (nb067AlphaDummy328 f) ≠ (nb067AlphaDummy335 f) from (by
                    unfold nb067AlphaDummy335;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0349 f) 0))))
                (TAlphaVar.there (show (nb067AlphaDummy326) ≠ (nb067AlphaDummy334) from
                    (by
                      unfold nb067AlphaDummy334;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0348) 1))))
                  (show (nb067AlphaDummy328 f) ≠ (nb067AlphaDummy336 f) from (by
                      unfold nb067AlphaDummy336;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0349 f) 1))))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb067AlphaDummy326))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb067AlphaDummy328 f))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb067AlphaDummy333) ≠ (nb067AlphaDummy340) from
                                    (by
                                      unfold nb067AlphaDummy340;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0352)
                                              1)))) (show
                                    (nb067AlphaDummy335 f) ≠ (nb067AlphaDummy343 f) from
                                    (by
                                      unfold nb067AlphaDummy343;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0353 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb067AlphaDummy333) ≠ (nb067AlphaDummy339) from (by
                                        unfold nb067AlphaDummy339;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0352)
                                                0)))) (show (nb067AlphaDummy335 f) ≠
                                        (nb067AlphaDummy342 f) from (by
                                        unfold nb067AlphaDummy342;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0353 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb067AlphaDummy333) ≠ (nb067AlphaDummy337) from
                                        (by
                                          unfold nb067AlphaDummy337;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb067_support_mem_0350)
                                                  0)))) (show (nb067AlphaDummy335 f) ≠
        (nb067AlphaDummy338 f) from (by
                                          unfold nb067AlphaDummy338;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb067_support_mem_0351 f) 0))))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.reflOfClosed
                                    [((nb067AlphaDummy341), (nb067AlphaDummy344 f)),
                                      ((nb067AlphaDummy340), (nb067AlphaDummy343 f)),
                                      ((nb067AlphaDummy339), (nb067AlphaDummy342 f)),
                                      ((nb067AlphaDummy337), (nb067AlphaDummy338 f)),
                                      ((nb067AlphaDummy333), (nb067AlphaDummy335 f)),
                                      ((nb067AlphaDummy334), (nb067AlphaDummy336 f)),
                                      ((nb067AlphaDummy326), (nb067AlphaDummy328 f)),
                                      ((nb067AlphaDummy325), (nb067AlphaDummy327 f)),
                                      ((nb067AlphaDummy331), (nb067AlphaDummy332 f)),
                                      ((nb067AlphaDummy329), (nb067AlphaDummy330 f)),
                                      ((nb067AlphaDummy322), (nb067AlphaDummy324 f)),
                                      ((nb067AlphaDummy321), (nb067AlphaDummy323 f)),
                                      ((nb067AlphaDummy000), f), ((nb067AlphaDummy003),
                                        (nb067AlphaDummy004 x y f)),
                                      ((nb067AlphaDummy002), y),
                                      ((nb067AlphaDummy001), x), ((nb067AlphaDummy005),
                                        (nb067AlphaDummy006 x y f))]
                                    (synC1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb067SplitAlpha0089 x y f))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (show (nb067AlphaDummy333) ≠ (nb067AlphaDummy337) from (by
                              unfold nb067AlphaDummy337;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0350) 0))))
                          (show (nb067AlphaDummy335 f) ≠ (nb067AlphaDummy338 f) from (by
                              unfold nb067AlphaDummy338;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0351 f) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb067AlphaDummy337), (nb067AlphaDummy338 f)),
                          ((nb067AlphaDummy333), (nb067AlphaDummy335 f)),
                          ((nb067AlphaDummy334), (nb067AlphaDummy336 f)),
                          ((nb067AlphaDummy326), (nb067AlphaDummy328 f)),
                          ((nb067AlphaDummy325), (nb067AlphaDummy327 f)),
                          ((nb067AlphaDummy331), (nb067AlphaDummy332 f)),
                          ((nb067AlphaDummy329), (nb067AlphaDummy330 f)),
                          ((nb067AlphaDummy322), (nb067AlphaDummy324 f)),
                          ((nb067AlphaDummy321), (nb067AlphaDummy323 f)),
                          ((nb067AlphaDummy000), f),
                          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb067AlphaDummy333) ≠ (nb067AlphaDummy337) from (by
                            unfold nb067AlphaDummy337;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0350) 0))))
                        (show (nb067AlphaDummy335 f) ≠ (nb067AlphaDummy338 f) from (by
                            unfold nb067AlphaDummy338;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0351 f) 0))))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (show (nb067AlphaDummy333) ≠ (nb067AlphaDummy337) from (by
                              unfold nb067AlphaDummy337;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0350) 0))))
                          (show (nb067AlphaDummy335 f) ≠ (nb067AlphaDummy338 f) from (by
                              unfold nb067AlphaDummy338;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0351 f) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb067AlphaDummy337), (nb067AlphaDummy338 f)),
                          ((nb067AlphaDummy333), (nb067AlphaDummy335 f)),
                          ((nb067AlphaDummy334), (nb067AlphaDummy336 f)),
                          ((nb067AlphaDummy326), (nb067AlphaDummy328 f)),
                          ((nb067AlphaDummy325), (nb067AlphaDummy327 f)),
                          ((nb067AlphaDummy331), (nb067AlphaDummy332 f)),
                          ((nb067AlphaDummy329), (nb067AlphaDummy330 f)),
                          ((nb067AlphaDummy322), (nb067AlphaDummy324 f)),
                          ((nb067AlphaDummy321), (nb067AlphaDummy323 f)),
                          ((nb067AlphaDummy000), f),
                          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0091`. -/
@[expose]
noncomputable def nb067SplitAlpha0091 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy341), (nb067AlphaDummy344 f)),
        ((nb067AlphaDummy340), (nb067AlphaDummy343 f)),
        ((nb067AlphaDummy339), (nb067AlphaDummy342 f)),
        ((nb067AlphaDummy337), (nb067AlphaDummy338 f)),
        ((nb067AlphaDummy333), (nb067AlphaDummy335 f)),
        ((nb067AlphaDummy334), (nb067AlphaDummy336 f)),
        ((nb067AlphaDummy359), (nb067AlphaDummy360 f)),
        ((nb067AlphaDummy357), (nb067AlphaDummy358 f)),
        ((nb067AlphaDummy326), (nb067AlphaDummy328 f)),
        ((nb067AlphaDummy325), (nb067AlphaDummy327 f)),
        ((nb067AlphaDummy355), (nb067AlphaDummy356 f)),
        ((nb067AlphaDummy329), (nb067AlphaDummy330 f)),
        ((nb067AlphaDummy322), (nb067AlphaDummy324 f)),
        ((nb067AlphaDummy321), (nb067AlphaDummy323 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb067AlphaDummy340)) (Class.cv (nb067AlphaDummy341)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb067AlphaDummy339))
            (synCun (Class.cv (nb067AlphaDummy340)) (Class.cv (nb067AlphaDummy341))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb067AlphaDummy343 f))
            (Class.cv (nb067AlphaDummy344 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy342 f))
            (synCun (Class.cv (nb067AlphaDummy343 f))
              (Class.cv (nb067AlphaDummy344 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy340) ≠ (nb067AlphaDummy347) from (by
                              unfold nb067AlphaDummy347;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0356) 0))))
                          (show (nb067AlphaDummy343 f) ≠ (nb067AlphaDummy348 f) from (by
                              unfold nb067AlphaDummy348;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0357 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy340) ≠ (nb067AlphaDummy345) from (by
                                unfold nb067AlphaDummy345;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0354) 0))))
                            (show (nb067AlphaDummy343 f) ≠ (nb067AlphaDummy346 f) from (by
                                unfold nb067AlphaDummy346;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0355 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy333))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy335 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy341) ≠ (nb067AlphaDummy347) from (by
                              unfold nb067AlphaDummy347;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0360) 0))))
                          (show (nb067AlphaDummy344 f) ≠ (nb067AlphaDummy348 f) from (by
                              unfold nb067AlphaDummy348;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0361 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy341) ≠ (nb067AlphaDummy345) from (by
                                unfold nb067AlphaDummy345;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0358) 0))))
                            (show (nb067AlphaDummy344 f) ≠ (nb067AlphaDummy346 f) from (by
                                unfold nb067AlphaDummy346;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0359 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy340) ≠ (nb067AlphaDummy347) from (by
                              unfold nb067AlphaDummy347;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0356) 0))))
                          (show (nb067AlphaDummy343 f) ≠ (nb067AlphaDummy348 f) from (by
                              unfold nb067AlphaDummy348;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0357 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy340) ≠ (nb067AlphaDummy345) from (by
                                unfold nb067AlphaDummy345;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0354) 0))))
                            (show (nb067AlphaDummy343 f) ≠ (nb067AlphaDummy346 f) from (by
                                unfold nb067AlphaDummy346;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0355 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy333))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy335 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy341) ≠ (nb067AlphaDummy347) from (by
                              unfold nb067AlphaDummy347;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0360) 0))))
                          (show (nb067AlphaDummy344 f) ≠ (nb067AlphaDummy348 f) from (by
                              unfold nb067AlphaDummy348;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0361 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy341) ≠ (nb067AlphaDummy345) from (by
                                unfold nb067AlphaDummy345;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0358) 0))))
                            (show (nb067AlphaDummy344 f) ≠ (nb067AlphaDummy346 f) from (by
                                unfold nb067AlphaDummy346;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0359 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb067AlphaDummy341), (nb067AlphaDummy344 f)),
          ((nb067AlphaDummy340), (nb067AlphaDummy343 f)),
          ((nb067AlphaDummy339), (nb067AlphaDummy342 f)),
          ((nb067AlphaDummy337), (nb067AlphaDummy338 f)),
          ((nb067AlphaDummy333), (nb067AlphaDummy335 f)),
          ((nb067AlphaDummy334), (nb067AlphaDummy336 f)),
          ((nb067AlphaDummy359), (nb067AlphaDummy360 f)),
          ((nb067AlphaDummy357), (nb067AlphaDummy358 f)),
          ((nb067AlphaDummy326), (nb067AlphaDummy328 f)),
          ((nb067AlphaDummy325), (nb067AlphaDummy327 f)),
          ((nb067AlphaDummy355), (nb067AlphaDummy356 f)),
          ((nb067AlphaDummy329), (nb067AlphaDummy330 f)),
          ((nb067AlphaDummy322), (nb067AlphaDummy324 f)),
          ((nb067AlphaDummy321), (nb067AlphaDummy323 f)), ((nb067AlphaDummy000), f),
          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy333))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067AlphaDummy335 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067AlphaDummy333))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067AlphaDummy335 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy340) ≠ (nb067AlphaDummy351) from (by
                                unfold nb067AlphaDummy351;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0364) 0))))
                            (show (nb067AlphaDummy343 f) ≠ (nb067AlphaDummy352 f) from (by
                                unfold nb067AlphaDummy352;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0365 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy340) ≠ (nb067AlphaDummy349) from (by
                                  unfold nb067AlphaDummy349;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0362) 0))))
                              (show (nb067AlphaDummy343 f) ≠ (nb067AlphaDummy350 f) from
                                (by
                                  unfold nb067AlphaDummy350;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0363 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy333))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy335 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy340) ≠ (nb067AlphaDummy351) from (by
                                unfold nb067AlphaDummy351;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0364) 0))))
                            (show (nb067AlphaDummy343 f) ≠ (nb067AlphaDummy352 f) from (by
                                unfold nb067AlphaDummy352;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0365 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy340) ≠ (nb067AlphaDummy349) from (by
                                  unfold nb067AlphaDummy349;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0362) 0))))
                              (show (nb067AlphaDummy343 f) ≠ (nb067AlphaDummy350 f) from
                                (by
                                  unfold nb067AlphaDummy350;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0363 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy333))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy335 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy341) ≠ (nb067AlphaDummy353) from (by
                                unfold nb067AlphaDummy353;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0368) 0))))
                            (show (nb067AlphaDummy344 f) ≠ (nb067AlphaDummy354 f) from (by
                                unfold nb067AlphaDummy354;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0369 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy341) ≠ (nb067AlphaDummy349) from (by
                                  unfold nb067AlphaDummy349;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0366) 0))))
                              (show (nb067AlphaDummy344 f) ≠ (nb067AlphaDummy350 f) from
                                (by
                                  unfold nb067AlphaDummy350;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0367 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy341) ≠ (nb067AlphaDummy353) from (by
                                unfold nb067AlphaDummy353;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0368) 0))))
                            (show (nb067AlphaDummy344 f) ≠ (nb067AlphaDummy354 f) from (by
                                unfold nb067AlphaDummy354;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0369 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy341) ≠ (nb067AlphaDummy349) from (by
                                  unfold nb067AlphaDummy349;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0366) 0))))
                              (show (nb067AlphaDummy344 f) ≠ (nb067AlphaDummy350 f) from
                                (by
                                  unfold nb067AlphaDummy350;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0367 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0092`. -/
@[expose]
noncomputable def nb067SplitAlpha0092 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy333), (nb067AlphaDummy335 f)),
        ((nb067AlphaDummy334), (nb067AlphaDummy336 f)),
        ((nb067AlphaDummy359), (nb067AlphaDummy360 f)),
        ((nb067AlphaDummy357), (nb067AlphaDummy358 f)),
        ((nb067AlphaDummy326), (nb067AlphaDummy328 f)),
        ((nb067AlphaDummy325), (nb067AlphaDummy327 f)),
        ((nb067AlphaDummy355), (nb067AlphaDummy356 f)),
        ((nb067AlphaDummy329), (nb067AlphaDummy330 f)),
        ((nb067AlphaDummy322), (nb067AlphaDummy324 f)),
        ((nb067AlphaDummy321), (nb067AlphaDummy323 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy333))
          (Class.cv (nb067AlphaDummy326))) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy334))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy333)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy333)) (synC1c))
              (Class.cv (nb067AlphaDummy333))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy335 f))
          (Class.cv (nb067AlphaDummy328 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy336 f))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy335 f)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy335 f)) (synC1c))
              (Class.cv (nb067AlphaDummy335 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067AlphaDummy326) ≠ (nb067AlphaDummy333) from (by
              unfold nb067AlphaDummy333;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0348) 0))))
          (show (nb067AlphaDummy328 f) ≠ (nb067AlphaDummy335 f) from (by
              unfold nb067AlphaDummy335;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0349 f) 0))))
          (TAlphaVar.there (show (nb067AlphaDummy326) ≠ (nb067AlphaDummy334) from (by
                unfold nb067AlphaDummy334;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0348) 1))))
            (show (nb067AlphaDummy328 f) ≠ (nb067AlphaDummy336 f) from (by
                unfold nb067AlphaDummy336;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0349 f) 1))))
            (TAlphaVar.there (show (nb067AlphaDummy326) ≠ (nb067AlphaDummy359) from (by
                  unfold nb067AlphaDummy359;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0378) 0))))
              (show (nb067AlphaDummy328 f) ≠ (nb067AlphaDummy360 f) from (by
                  unfold nb067AlphaDummy360;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0379 f) 0))))
              (TAlphaVar.there (show (nb067AlphaDummy326) ≠ (nb067AlphaDummy357) from (by
                    unfold nb067AlphaDummy357;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0376) 0))))
                (show (nb067AlphaDummy328 f) ≠ (nb067AlphaDummy358 f) from (by
                    unfold nb067AlphaDummy358;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0377 f) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy326))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb067AlphaDummy328 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb067AlphaDummy333) ≠ (nb067AlphaDummy340) from (by
                                  unfold nb067AlphaDummy340;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0352) 1))))
                              (show (nb067AlphaDummy335 f) ≠ (nb067AlphaDummy343 f) from
                                (by
                                  unfold nb067AlphaDummy343;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0353 f) 1))))
                              (TAlphaVar.there
                                (show (nb067AlphaDummy333) ≠ (nb067AlphaDummy339) from (by
                                    unfold nb067AlphaDummy339;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0352) 0)))) (show
                                  (nb067AlphaDummy335 f) ≠ (nb067AlphaDummy342 f) from (by
                                    unfold nb067AlphaDummy342;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0353 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb067AlphaDummy333) ≠ (nb067AlphaDummy337) from
                                    (by
                                      unfold nb067AlphaDummy337;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0350)
                                              0)))) (show
                                    (nb067AlphaDummy335 f) ≠ (nb067AlphaDummy338 f) from
                                    (by
                                      unfold nb067AlphaDummy338;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0351 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb067AlphaDummy341), (nb067AlphaDummy344 f)),
                                  ((nb067AlphaDummy340), (nb067AlphaDummy343 f)),
                                  ((nb067AlphaDummy339), (nb067AlphaDummy342 f)),
                                  ((nb067AlphaDummy337), (nb067AlphaDummy338 f)),
                                  ((nb067AlphaDummy333), (nb067AlphaDummy335 f)),
                                  ((nb067AlphaDummy334), (nb067AlphaDummy336 f)),
                                  ((nb067AlphaDummy359), (nb067AlphaDummy360 f)),
                                  ((nb067AlphaDummy357), (nb067AlphaDummy358 f)),
                                  ((nb067AlphaDummy326), (nb067AlphaDummy328 f)),
                                  ((nb067AlphaDummy325), (nb067AlphaDummy327 f)),
                                  ((nb067AlphaDummy355), (nb067AlphaDummy356 f)),
                                  ((nb067AlphaDummy329), (nb067AlphaDummy330 f)),
                                  ((nb067AlphaDummy322), (nb067AlphaDummy324 f)),
                                  ((nb067AlphaDummy321), (nb067AlphaDummy323 f)),
                                  ((nb067AlphaDummy000), f), ((nb067AlphaDummy003),
                                    (nb067AlphaDummy004 x y f)),
                                  ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                                  ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb067SplitAlpha0091 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb067AlphaDummy333) ≠ (nb067AlphaDummy337) from (by
                          unfold nb067AlphaDummy337;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0350) 0))))
                      (show (nb067AlphaDummy335 f) ≠ (nb067AlphaDummy338 f) from (by
                          unfold nb067AlphaDummy338;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0351 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb067AlphaDummy337), (nb067AlphaDummy338 f)),
                      ((nb067AlphaDummy333), (nb067AlphaDummy335 f)),
                      ((nb067AlphaDummy334), (nb067AlphaDummy336 f)),
                      ((nb067AlphaDummy359), (nb067AlphaDummy360 f)),
                      ((nb067AlphaDummy357), (nb067AlphaDummy358 f)),
                      ((nb067AlphaDummy326), (nb067AlphaDummy328 f)),
                      ((nb067AlphaDummy325), (nb067AlphaDummy327 f)),
                      ((nb067AlphaDummy355), (nb067AlphaDummy356 f)),
                      ((nb067AlphaDummy329), (nb067AlphaDummy330 f)),
                      ((nb067AlphaDummy322), (nb067AlphaDummy324 f)),
                      ((nb067AlphaDummy321), (nb067AlphaDummy323 f)),
                      ((nb067AlphaDummy000), f),
                      ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                      ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                      ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067AlphaDummy333) ≠ (nb067AlphaDummy337) from
                      (by
                        unfold nb067AlphaDummy337;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0350) 0))))
                    (show (nb067AlphaDummy335 f) ≠ (nb067AlphaDummy338 f) from (by
                        unfold nb067AlphaDummy338;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0351 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb067AlphaDummy333) ≠ (nb067AlphaDummy337) from (by
                          unfold nb067AlphaDummy337;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0350) 0))))
                      (show (nb067AlphaDummy335 f) ≠ (nb067AlphaDummy338 f) from (by
                          unfold nb067AlphaDummy338;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0351 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb067AlphaDummy337), (nb067AlphaDummy338 f)),
                      ((nb067AlphaDummy333), (nb067AlphaDummy335 f)),
                      ((nb067AlphaDummy334), (nb067AlphaDummy336 f)),
                      ((nb067AlphaDummy359), (nb067AlphaDummy360 f)),
                      ((nb067AlphaDummy357), (nb067AlphaDummy358 f)),
                      ((nb067AlphaDummy326), (nb067AlphaDummy328 f)),
                      ((nb067AlphaDummy325), (nb067AlphaDummy327 f)),
                      ((nb067AlphaDummy355), (nb067AlphaDummy356 f)),
                      ((nb067AlphaDummy329), (nb067AlphaDummy330 f)),
                      ((nb067AlphaDummy322), (nb067AlphaDummy324 f)),
                      ((nb067AlphaDummy321), (nb067AlphaDummy323 f)),
                      ((nb067AlphaDummy000), f),
                      ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                      ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                      ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0093`. -/
@[expose]
noncomputable def nb067SplitAlpha0093 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy355), (nb067AlphaDummy356 f)),
        ((nb067AlphaDummy329), (nb067AlphaDummy330 f)),
        ((nb067AlphaDummy322), (nb067AlphaDummy324 f)),
        ((nb067AlphaDummy321), (nb067AlphaDummy323 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy355))
          (Class.cab (nb067AlphaDummy325)
            (synWrex (nb067AlphaDummy326) (Class.cv (nb067AlphaDummy321))
              (Wff.classEq (Class.cv (nb067AlphaDummy325))
                (synCun (synCphi (Class.cv (nb067AlphaDummy326))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb067AlphaDummy355))
            (Class.cab (nb067AlphaDummy325)
              (synWrex (nb067AlphaDummy326) (Class.cv (nb067AlphaDummy321))
                (Wff.classEq (Class.cv (nb067AlphaDummy325))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy326)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy356 f))
          (Class.cab (nb067AlphaDummy327 f)
            (synWrex (nb067AlphaDummy328 f) (Class.cv (nb067AlphaDummy323 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy327 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy328 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb067AlphaDummy356 f))
            (Class.cab (nb067AlphaDummy327 f)
              (synWrex (nb067AlphaDummy328 f) (Class.cv (nb067AlphaDummy323 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy327 f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy328 f)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb067AlphaDummy321) ≠ (nb067AlphaDummy326) from
                    (by
                      unfold nb067AlphaDummy326;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0370) 1))))
                  (show (nb067AlphaDummy323 f) ≠ (nb067AlphaDummy328 f) from (by
                      unfold nb067AlphaDummy328;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0372 f) 1))))
                  (TAlphaVar.there (show (nb067AlphaDummy321) ≠ (nb067AlphaDummy325) from
                      (by
                        unfold nb067AlphaDummy325;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0370) 0))))
                    (show (nb067AlphaDummy323 f) ≠ (nb067AlphaDummy327 f) from (by
                        unfold nb067AlphaDummy327;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0372 f) 0)))) (TAlphaVar.there
                      (show (nb067AlphaDummy321) ≠ (nb067AlphaDummy355) from (by
                          unfold nb067AlphaDummy355;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0374) 0))))
                      (show (nb067AlphaDummy323 f) ≠ (nb067AlphaDummy356 f) from (by
                          unfold nb067AlphaDummy356;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0375 f) 0))))
                      (TAlphaVar.there
                        (show (nb067AlphaDummy321) ≠ (nb067AlphaDummy329) from (by
                            unfold nb067AlphaDummy329;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0371) 0))))
                        (show (nb067AlphaDummy323 f) ≠ (nb067AlphaDummy330 f) from (by
                            unfold nb067AlphaDummy330;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0373 f) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb067AlphaDummy000))).fv ∪ ((synCvv)).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv f)).fv ∪ ((synCvv)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb067AlphaDummy322))).fv ∪
                      ((Class.cv (nb067AlphaDummy321))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb067AlphaDummy324 f))).fv ∪
                      ((Class.cv (nb067AlphaDummy323 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067SplitAlpha0092 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067SplitAlpha0092 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb067AlphaDummy357), (nb067AlphaDummy358 f)),
                          ((nb067AlphaDummy326), (nb067AlphaDummy328 f)),
                          ((nb067AlphaDummy325), (nb067AlphaDummy327 f)),
                          ((nb067AlphaDummy355), (nb067AlphaDummy356 f)),
                          ((nb067AlphaDummy329), (nb067AlphaDummy330 f)),
                          ((nb067AlphaDummy322), (nb067AlphaDummy324 f)),
                          ((nb067AlphaDummy321), (nb067AlphaDummy323 f)),
                          ((nb067AlphaDummy000), f),
                          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067AlphaDummy321) ≠ (nb067AlphaDummy326) from
                      (by
                        unfold nb067AlphaDummy326;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0370) 1))))
                    (show (nb067AlphaDummy323 f) ≠ (nb067AlphaDummy328 f) from (by
                        unfold nb067AlphaDummy328;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0372 f) 1)))) (TAlphaVar.there
                      (show (nb067AlphaDummy321) ≠ (nb067AlphaDummy325) from (by
                          unfold nb067AlphaDummy325;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0370) 0))))
                      (show (nb067AlphaDummy323 f) ≠ (nb067AlphaDummy327 f) from (by
                          unfold nb067AlphaDummy327;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0372 f) 0))))
                      (TAlphaVar.there
                        (show (nb067AlphaDummy321) ≠ (nb067AlphaDummy355) from (by
                            unfold nb067AlphaDummy355;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0374) 0))))
                        (show (nb067AlphaDummy323 f) ≠ (nb067AlphaDummy356 f) from (by
                            unfold nb067AlphaDummy356;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0375 f) 0))))
                        (TAlphaVar.there
                          (show (nb067AlphaDummy321) ≠ (nb067AlphaDummy329) from (by
                              unfold nb067AlphaDummy329;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0371) 0))))
                          (show (nb067AlphaDummy323 f) ≠ (nb067AlphaDummy330 f) from (by
                              unfold nb067AlphaDummy330;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0373 f) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb067AlphaDummy000))).fv ∪ ((synCvv)).fv)
                              (by decide))
                            (freshVar_injective (((Class.cv f)).fv ∪ ((synCvv)).fv)
                              (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb067AlphaDummy322))).fv ∪
                        ((Class.cv (nb067AlphaDummy321))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb067AlphaDummy324 f))).fv ∪
                        ((Class.cv (nb067AlphaDummy323 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067SplitAlpha0092 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067SplitAlpha0092 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb067AlphaDummy357), (nb067AlphaDummy358 f)),
                            ((nb067AlphaDummy326), (nb067AlphaDummy328 f)),
                            ((nb067AlphaDummy325), (nb067AlphaDummy327 f)),
                            ((nb067AlphaDummy355), (nb067AlphaDummy356 f)),
                            ((nb067AlphaDummy329), (nb067AlphaDummy330 f)),
                            ((nb067AlphaDummy322), (nb067AlphaDummy324 f)),
                            ((nb067AlphaDummy321), (nb067AlphaDummy323 f)),
                            ((nb067AlphaDummy000), f),
                            ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                            ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                            ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part035`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0094`. -/
@[expose]
noncomputable def nb067SplitAlpha0094 (x : Var) (y : Var) (f : Var) (dv_f_x : f ≠ x)
    (dv_f_y : f ≠ y) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classEq (Class.cv (nb067AlphaDummy005)) (synCop
            (synCop (Class.cv (nb067AlphaDummy001)) (Class.cv (nb067AlphaDummy002)))
            (Class.cv (nb067AlphaDummy003)))) (Wff.neg (synWa
            (synWa (Wff.classMem (Class.cv (nb067AlphaDummy001)) (synCvv))
              (Wff.classMem (Class.cv (nb067AlphaDummy002)) (synCvv)))
            (Wff.classEq (Class.cv (nb067AlphaDummy003)) (Class.cab (nb067AlphaDummy000)
                (synWf (Class.cv (nb067AlphaDummy000)) (Class.cv (nb067AlphaDummy002))
                  (Class.cv (nb067AlphaDummy001))))))))
      (Wff.imp (Wff.classEq (Class.cv (nb067AlphaDummy006 x y f))
          (synCop (synCop (Class.cv x) (Class.cv y))
            (Class.cv (nb067AlphaDummy004 x y f)))) (Wff.neg (synWa
            (synWa (Wff.classMem (Class.cv x) (synCvv)) (Wff.classMem (Class.cv y) (synCvv)))
            (Wff.classEq (Class.cv (nb067AlphaDummy004 x y f))
              (Class.cab f (synWf (Class.cv f) (Class.cv y) (Class.cv x))))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
            (show (nb067AlphaDummy003) ≠ (nb067AlphaDummy005) from (by
                unfold nb067AlphaDummy005;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0004) 0))))) (Ne.symm
            (show (nb067AlphaDummy004 x y f) ≠ (nb067AlphaDummy006 x y f) from (by
                unfold nb067AlphaDummy006;
                with_reducible
                  exact
                    (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0005 x y f) 0)))))
          (TAlphaVar.there (Ne.symm (show (nb067AlphaDummy002) ≠ (nb067AlphaDummy005) from
                (by
                  unfold nb067AlphaDummy005;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0002) 0)))))
            (Ne.symm (show y ≠ (nb067AlphaDummy006 x y f) from (by
                  unfold nb067AlphaDummy006;
                  with_reducible
                    exact
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0003 x y f) 0)))))
            (TAlphaVar.there (Ne.symm
                (show (nb067AlphaDummy001) ≠ (nb067AlphaDummy005) from (by
                    unfold nb067AlphaDummy005;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0000) 0)))))
              (Ne.symm (show x ≠ (nb067AlphaDummy006 x y f) from (by
                    unfold nb067AlphaDummy006;
                    with_reducible
                      exact
                        (Nat.ne_of_lt
                          (mem_lt_freshVar (nb067_support_mem_0001 x y f) 0)))))
              (TAlphaVar.here _ _ _))))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb067SplitAlpha0009 x y f dv_x_y))))) (TAlphaWff.neg
      (TAlphaWff.conj (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                (show (nb067AlphaDummy001) ≠ (nb067AlphaDummy003) from (by
                    unfold nb067AlphaDummy003;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0006) 0))))
                (show x ≠ (nb067AlphaDummy004 x y f) from (by
                    unfold nb067AlphaDummy004;
                    with_reducible
                      exact
                        (Nat.ne_of_lt
                          (mem_lt_freshVar (nb067_support_mem_0007 x y f) 0))))
                (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                  dv_x_y (TAlphaVar.here _ _ _)))) (TAlphaClass.reflOfClosed
              [((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
              (synCvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem (TAlphaClass.cv
              (TAlphaVar.there (show (nb067AlphaDummy002) ≠ (nb067AlphaDummy003) from (by
                    unfold nb067AlphaDummy003;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0042) 0))))
                (show y ≠ (nb067AlphaDummy004 x y f) from (by
                    unfold nb067AlphaDummy004;
                    with_reducible
                      exact
                        (Nat.ne_of_lt
                          (mem_lt_freshVar (nb067_support_mem_0043 x y f) 0))))
                (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
              [((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
              (synCvv) (by simp only [fv_syn_cvv]))))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.conj (TAlphaWff.neg (nb067SplitAlpha0082 x y f dv_f_y))
              (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                              (nb067SplitAlpha0088 x y f dv_f_x dv_x_y)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                              (nb067SplitAlpha0088 x y f dv_f_x dv_x_y))))))))
                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb067AlphaDummy322), (nb067AlphaDummy324 f)),
                            ((nb067AlphaDummy321), (nb067AlphaDummy323 f)),
                            ((nb067AlphaDummy000), f),
                            ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                            ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                            ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                          (synCvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb067AlphaDummy322) ≠ (nb067AlphaDummy326) from (by
          unfold nb067AlphaDummy326;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0342)
                  1)))) (show (nb067AlphaDummy324 f) ≠ (nb067AlphaDummy328 f) from (by
          unfold nb067AlphaDummy328;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0344 f)
                  1)))) (TAlphaVar.there (show (nb067AlphaDummy322) ≠ (nb067AlphaDummy325)
        from (by
          unfold nb067AlphaDummy325;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0342)
                  0)))) (show (nb067AlphaDummy324 f) ≠ (nb067AlphaDummy327 f) from (by
          unfold nb067AlphaDummy327;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0344
                    f)
                  0)))) (TAlphaVar.there (show (nb067AlphaDummy322) ≠ (nb067AlphaDummy331)
        from (by
          unfold nb067AlphaDummy331;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0346)
                  0)))) (show (nb067AlphaDummy324 f) ≠ (nb067AlphaDummy332 f) from (by
          unfold nb067AlphaDummy332;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0347
                    f)
                  0)))) (TAlphaVar.there (show (nb067AlphaDummy322) ≠ (nb067AlphaDummy329)
        from (by
          unfold
            nb067AlphaDummy329;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0343)
                  0)))) (show (nb067AlphaDummy324 f) ≠ (nb067AlphaDummy330 f) from (by
          unfold
            nb067AlphaDummy330;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0345
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb067SplitAlpha0090 x y f)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb067AlphaDummy322) ≠ (nb067AlphaDummy326) from (by
          unfold nb067AlphaDummy326;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0342)
                  1)))) (show (nb067AlphaDummy324 f) ≠ (nb067AlphaDummy328 f) from (by
          unfold nb067AlphaDummy328;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0344 f)
                  1)))) (TAlphaVar.there (show (nb067AlphaDummy322) ≠ (nb067AlphaDummy325)
        from (by
          unfold nb067AlphaDummy325;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0342)
                  0)))) (show (nb067AlphaDummy324 f) ≠ (nb067AlphaDummy327 f) from (by
          unfold nb067AlphaDummy327;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0344
                    f)
                  0)))) (TAlphaVar.there (show (nb067AlphaDummy322) ≠ (nb067AlphaDummy331)
        from (by
          unfold nb067AlphaDummy331;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0346)
                  0)))) (show (nb067AlphaDummy324 f) ≠ (nb067AlphaDummy332 f) from (by
          unfold nb067AlphaDummy332;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0347
                    f)
                  0)))) (TAlphaVar.there (show (nb067AlphaDummy322) ≠ (nb067AlphaDummy329)
        from (by
          unfold
            nb067AlphaDummy329;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0343)
                  0)))) (show (nb067AlphaDummy324 f) ≠ (nb067AlphaDummy330 f) from (by
          unfold
            nb067AlphaDummy330;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0345
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb067SplitAlpha0090 x y f)))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.neg (nb067SplitAlpha0093 x y f))))))))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy000) ≠ (nb067AlphaDummy322) from (by
                                unfold nb067AlphaDummy322;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0384) 1))))
                            (show f ≠ (nb067AlphaDummy324 f) from (by
                                unfold nb067AlphaDummy324;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0385 f) 1))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy000) ≠ (nb067AlphaDummy321) from (by
                                  unfold nb067AlphaDummy321;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0384) 0))))
                              (show f ≠ (nb067AlphaDummy323 f) from (by
                                  unfold nb067AlphaDummy323;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0385 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nominal_df_map`. -/
@[expose]
noncomputable def nominalDfMap (x : Var) (y : Var) (f : Var) (dv_f_x : f ≠ x)
    (dv_f_y : f ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (synCmap)
        (synCmpt2 x (synCvv) y (synCvv) (.cab f (synWf (.cv f) (.cv y) (.cv x))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.ex
              (TAlphaWff.neg (nb067SplitAlpha0094 x y f dv_f_x dv_f_y dv_x_y))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
