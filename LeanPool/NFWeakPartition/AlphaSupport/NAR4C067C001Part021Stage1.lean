/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C067C001Block004

/-! NF weak partition development: NAR4C067C001Part021. -/


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
noncomputable def nb067_split_alpha_0036 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_271), (nb067_alpha_dummy_272 f)),
        ((nb067_alpha_dummy_245), (nb067_alpha_dummy_246 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
        ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_271))
          (Class.cab (nb067_alpha_dummy_241)
            (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_084))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_241))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_242))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb067_alpha_dummy_271))
            (Class.cab (nb067_alpha_dummy_241)
              (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_084))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_241))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_242)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_272 f))
          (Class.cab (nb067_alpha_dummy_243 f)
            (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_087 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb067_alpha_dummy_272 f))
            (Class.cab (nb067_alpha_dummy_243 f)
              (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_087 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb067_alpha_dummy_084) ≠ (nb067_alpha_dummy_242) from
                    (by
                      unfold nb067_alpha_dummy_242;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0292) 1))))
                  (show (nb067_alpha_dummy_087 f) ≠ (nb067_alpha_dummy_244 f) from (by
                      unfold nb067_alpha_dummy_244;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0294 f) 1))))
                  (TAlphaVar.there (show (nb067_alpha_dummy_084) ≠ (nb067_alpha_dummy_241) from
                      (by
                        unfold nb067_alpha_dummy_241;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0292) 0))))
                    (show (nb067_alpha_dummy_087 f) ≠ (nb067_alpha_dummy_243 f) from (by
                        unfold nb067_alpha_dummy_243;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0294 f) 0)))) (TAlphaVar.there
                      (show (nb067_alpha_dummy_084) ≠ (nb067_alpha_dummy_271) from (by
                          unfold nb067_alpha_dummy_271;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0296) 0))))
                      (show (nb067_alpha_dummy_087 f) ≠ (nb067_alpha_dummy_272 f) from (by
                          unfold nb067_alpha_dummy_272;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0297 f) 0))))
                      (TAlphaVar.there
                        (show (nb067_alpha_dummy_084) ≠ (nb067_alpha_dummy_245) from (by
                            unfold nb067_alpha_dummy_245;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0293) 0))))
                        (show (nb067_alpha_dummy_087 f) ≠ (nb067_alpha_dummy_246 f) from (by
                            unfold nb067_alpha_dummy_246;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0295 f) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb067_alpha_dummy_000))).fv ∪
                              ((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv) (by decide))
                          (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb067_alpha_dummy_085))).fv ∪
                      ((Class.cv (nb067_alpha_dummy_084))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb067_alpha_dummy_088 f))).fv ∪
                      ((Class.cv (nb067_alpha_dummy_087 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb067_alpha_dummy_242) ≠
        (nb067_alpha_dummy_249) from (by
          unfold nb067_alpha_dummy_249;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0270) 0)))) (show (nb067_alpha_dummy_244 f) ≠
        (nb067_alpha_dummy_251 f) from (by
          unfold nb067_alpha_dummy_251;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0271 f) 0)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_242) ≠ (nb067_alpha_dummy_250) from (by
          unfold nb067_alpha_dummy_250;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0270) 1)))) (show (nb067_alpha_dummy_244 f) ≠
        (nb067_alpha_dummy_252 f) from (by
          unfold nb067_alpha_dummy_252;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0271 f) 1)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_242) ≠ (nb067_alpha_dummy_275) from (by
          unfold nb067_alpha_dummy_275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0300) 0)))) (show (nb067_alpha_dummy_244 f) ≠
        (nb067_alpha_dummy_276 f) from (by
          unfold nb067_alpha_dummy_276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0301 f) 0)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_242) ≠ (nb067_alpha_dummy_273) from (by
          unfold nb067_alpha_dummy_273;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0298) 0)))) (show (nb067_alpha_dummy_244 f) ≠
        (nb067_alpha_dummy_274 f) from (by
          unfold nb067_alpha_dummy_274;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0299 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb067_split_alpha_0035 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb067_alpha_dummy_242) ≠
        (nb067_alpha_dummy_249) from (by
          unfold nb067_alpha_dummy_249;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0270) 0)))) (show (nb067_alpha_dummy_244 f) ≠
        (nb067_alpha_dummy_251 f) from (by
          unfold nb067_alpha_dummy_251;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0271 f) 0)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_242) ≠ (nb067_alpha_dummy_250) from (by
          unfold nb067_alpha_dummy_250;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0270) 1)))) (show (nb067_alpha_dummy_244 f) ≠
        (nb067_alpha_dummy_252 f) from (by
          unfold nb067_alpha_dummy_252;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0271 f) 1)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_242) ≠ (nb067_alpha_dummy_275) from (by
          unfold nb067_alpha_dummy_275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0300) 0)))) (show (nb067_alpha_dummy_244 f) ≠
        (nb067_alpha_dummy_276 f) from (by
          unfold nb067_alpha_dummy_276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0301 f) 0)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_242) ≠ (nb067_alpha_dummy_273) from (by
          unfold nb067_alpha_dummy_273;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0298) 0)))) (show (nb067_alpha_dummy_244 f) ≠
        (nb067_alpha_dummy_274 f) from (by
          unfold nb067_alpha_dummy_274;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0299 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb067_split_alpha_0035 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb067_alpha_dummy_273), (nb067_alpha_dummy_274 f)),
                          ((nb067_alpha_dummy_242), (nb067_alpha_dummy_244 f)),
                          ((nb067_alpha_dummy_241), (nb067_alpha_dummy_243 f)),
                          ((nb067_alpha_dummy_271), (nb067_alpha_dummy_272 f)),
                          ((nb067_alpha_dummy_245), (nb067_alpha_dummy_246 f)),
                          ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                          ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                          ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                          ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                          ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
                          ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
                          ((nb067_alpha_dummy_000), f),
                          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067_alpha_dummy_084) ≠ (nb067_alpha_dummy_242) from
                      (by
                        unfold nb067_alpha_dummy_242;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0292) 1))))
                    (show (nb067_alpha_dummy_087 f) ≠ (nb067_alpha_dummy_244 f) from (by
                        unfold nb067_alpha_dummy_244;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0294 f) 1)))) (TAlphaVar.there
                      (show (nb067_alpha_dummy_084) ≠ (nb067_alpha_dummy_241) from (by
                          unfold nb067_alpha_dummy_241;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0292) 0))))
                      (show (nb067_alpha_dummy_087 f) ≠ (nb067_alpha_dummy_243 f) from (by
                          unfold nb067_alpha_dummy_243;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0294 f) 0))))
                      (TAlphaVar.there
                        (show (nb067_alpha_dummy_084) ≠ (nb067_alpha_dummy_271) from (by
                            unfold nb067_alpha_dummy_271;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0296) 0))))
                        (show (nb067_alpha_dummy_087 f) ≠ (nb067_alpha_dummy_272 f) from (by
                            unfold nb067_alpha_dummy_272;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0297 f) 0))))
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_084) ≠ (nb067_alpha_dummy_245) from (by
                              unfold nb067_alpha_dummy_245;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0293) 0))))
                          (show (nb067_alpha_dummy_087 f) ≠ (nb067_alpha_dummy_246 f) from (by
                              unfold nb067_alpha_dummy_246;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0295 f) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb067_alpha_dummy_000))).fv ∪
                                ((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb067_alpha_dummy_085))).fv ∪
                        ((Class.cv (nb067_alpha_dummy_084))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb067_alpha_dummy_088 f))).fv ∪
                        ((Class.cv (nb067_alpha_dummy_087 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067_alpha_dummy_242) ≠ (nb067_alpha_dummy_249) from (by
          unfold nb067_alpha_dummy_249;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0270) 0)))) (show (nb067_alpha_dummy_244 f) ≠
        (nb067_alpha_dummy_251 f) from (by
          unfold nb067_alpha_dummy_251;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0271 f) 0)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_242) ≠ (nb067_alpha_dummy_250) from (by
          unfold nb067_alpha_dummy_250;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0270) 1)))) (show (nb067_alpha_dummy_244 f) ≠
        (nb067_alpha_dummy_252 f) from (by
          unfold nb067_alpha_dummy_252;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0271 f) 1)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_242) ≠ (nb067_alpha_dummy_275) from (by
          unfold nb067_alpha_dummy_275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0300) 0)))) (show (nb067_alpha_dummy_244 f) ≠
        (nb067_alpha_dummy_276 f) from (by
          unfold nb067_alpha_dummy_276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0301 f)
                  0)))) (TAlphaVar.there (show (nb067_alpha_dummy_242) ≠ (nb067_alpha_dummy_273)
        from (by
          unfold nb067_alpha_dummy_273;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0298)
                  0)))) (show (nb067_alpha_dummy_244 f) ≠ (nb067_alpha_dummy_274 f) from (by
          unfold nb067_alpha_dummy_274;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0299 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb067_split_alpha_0035 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067_alpha_dummy_242) ≠ (nb067_alpha_dummy_249) from (by
          unfold nb067_alpha_dummy_249;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0270) 0)))) (show (nb067_alpha_dummy_244 f) ≠
        (nb067_alpha_dummy_251 f) from (by
          unfold nb067_alpha_dummy_251;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0271 f) 0)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_242) ≠ (nb067_alpha_dummy_250) from (by
          unfold nb067_alpha_dummy_250;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0270) 1)))) (show (nb067_alpha_dummy_244 f) ≠
        (nb067_alpha_dummy_252 f) from (by
          unfold nb067_alpha_dummy_252;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0271 f) 1)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_242) ≠ (nb067_alpha_dummy_275) from (by
          unfold nb067_alpha_dummy_275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0300) 0)))) (show (nb067_alpha_dummy_244 f) ≠
        (nb067_alpha_dummy_276 f) from (by
          unfold nb067_alpha_dummy_276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0301 f)
                  0)))) (TAlphaVar.there (show (nb067_alpha_dummy_242) ≠ (nb067_alpha_dummy_273)
        from (by
          unfold nb067_alpha_dummy_273;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0298)
                  0)))) (show (nb067_alpha_dummy_244 f) ≠ (nb067_alpha_dummy_274 f) from (by
          unfold nb067_alpha_dummy_274;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0299 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb067_split_alpha_0035 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb067_alpha_dummy_273), (nb067_alpha_dummy_274 f)),
                            ((nb067_alpha_dummy_242), (nb067_alpha_dummy_244 f)),
                            ((nb067_alpha_dummy_241), (nb067_alpha_dummy_243 f)),
                            ((nb067_alpha_dummy_271), (nb067_alpha_dummy_272 f)),
                            ((nb067_alpha_dummy_245), (nb067_alpha_dummy_246 f)),
                            ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                            ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                            ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                            ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                            ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
                            ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
                            ((nb067_alpha_dummy_000), f),
                            ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                            ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                            ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

@[expose]
noncomputable def nb067_split_alpha_0037 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
        ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (syn_wbr (Class.cv (nb067_alpha_dummy_083))
          (syn_ccnv (Class.cv (nb067_alpha_dummy_000))) (Class.cv (nb067_alpha_dummy_085)))
        (Wff.neg (syn_wbr (Class.cv (nb067_alpha_dummy_085)) (Class.cv (nb067_alpha_dummy_000))
            (Class.cv (nb067_alpha_dummy_084)))))
      (Wff.imp (syn_wbr (Class.cv (nb067_alpha_dummy_086 f)) (syn_ccnv (Class.cv f))
          (Class.cv (nb067_alpha_dummy_088 f))) (Wff.neg
          (syn_wbr (Class.cv (nb067_alpha_dummy_088 f)) (Class.cv f)
            (Class.cv (nb067_alpha_dummy_087 f))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb067_alpha_dummy_083) ≠ (nb067_alpha_dummy_128) from
                                    (by
                                      unfold nb067_alpha_dummy_128;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0134)
                                              1)))) (show
                                    (nb067_alpha_dummy_086 f) ≠ (nb067_alpha_dummy_130 f) from
                                    (by
                                      unfold nb067_alpha_dummy_130;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0136 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb067_alpha_dummy_083) ≠ (nb067_alpha_dummy_127) from (by
                                        unfold nb067_alpha_dummy_127;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0134)
                                                0)))) (show (nb067_alpha_dummy_086 f) ≠
                                        (nb067_alpha_dummy_129 f) from (by
                                        unfold nb067_alpha_dummy_129;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0136 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb067_alpha_dummy_083) ≠ (nb067_alpha_dummy_133) from
                                        (by
                                          unfold nb067_alpha_dummy_133;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb067_support_mem_0138)
                                                  0)))) (show (nb067_alpha_dummy_086 f) ≠
        (nb067_alpha_dummy_134 f) from (by
                                          unfold nb067_alpha_dummy_134;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb067_support_mem_0139 f) 0))))
                                      (TAlphaVar.there (show (nb067_alpha_dummy_083) ≠
        (nb067_alpha_dummy_131) from (by
          unfold nb067_alpha_dummy_131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0135) 0)))) (show (nb067_alpha_dummy_086 f) ≠
        (nb067_alpha_dummy_132 f) from (by
          unfold nb067_alpha_dummy_132;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0137 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_ccnv
        (Class.cv (nb067_alpha_dummy_000)))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv
        (nb067_alpha_dummy_000)))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪
        ((syn_ccnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb067_alpha_dummy_083))).fv ∪
                                      ((Class.cv (nb067_alpha_dummy_085))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪
                                      ((Class.cv (nb067_alpha_dummy_088 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067_split_alpha_0016 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb067_alpha_dummy_083) ≠ (nb067_alpha_dummy_128) from
                                    (by
                                      unfold nb067_alpha_dummy_128;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0134)
                                              1)))) (show
                                    (nb067_alpha_dummy_086 f) ≠ (nb067_alpha_dummy_130 f) from
                                    (by
                                      unfold nb067_alpha_dummy_130;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0136 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb067_alpha_dummy_083) ≠ (nb067_alpha_dummy_127) from (by
                                        unfold nb067_alpha_dummy_127;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0134)
                                                0)))) (show (nb067_alpha_dummy_086 f) ≠
                                        (nb067_alpha_dummy_129 f) from (by
                                        unfold nb067_alpha_dummy_129;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0136 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb067_alpha_dummy_083) ≠ (nb067_alpha_dummy_133) from
                                        (by
                                          unfold nb067_alpha_dummy_133;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb067_support_mem_0138)
                                                  0)))) (show (nb067_alpha_dummy_086 f) ≠
        (nb067_alpha_dummy_134 f) from (by
                                          unfold nb067_alpha_dummy_134;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb067_support_mem_0139 f) 0))))
                                      (TAlphaVar.there (show (nb067_alpha_dummy_083) ≠
        (nb067_alpha_dummy_131) from (by
          unfold nb067_alpha_dummy_131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0135) 0)))) (show (nb067_alpha_dummy_086 f) ≠
        (nb067_alpha_dummy_132 f) from (by
          unfold nb067_alpha_dummy_132;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0137 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_ccnv
        (Class.cv (nb067_alpha_dummy_000)))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv
        (nb067_alpha_dummy_000)))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪
        ((syn_ccnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb067_alpha_dummy_083))).fv ∪
                                      ((Class.cv (nb067_alpha_dummy_085))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪
                                      ((Class.cv (nb067_alpha_dummy_088 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067_split_alpha_0016 x y f)))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb067_split_alpha_0019 x y f))))))))
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg (nb067_split_alpha_0031 x y f)))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb067_alpha_dummy_085) ≠ (nb067_alpha_dummy_242) from (by
                                        unfold nb067_alpha_dummy_242;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0264)
                                                1)))) (show (nb067_alpha_dummy_088 f) ≠
                                        (nb067_alpha_dummy_244 f) from (by
                                        unfold nb067_alpha_dummy_244;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0266 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb067_alpha_dummy_085) ≠ (nb067_alpha_dummy_241) from
                                        (by
                                          unfold nb067_alpha_dummy_241;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb067_support_mem_0264)
                                                  0)))) (show (nb067_alpha_dummy_088 f) ≠
        (nb067_alpha_dummy_243 f) from (by
                                          unfold nb067_alpha_dummy_243;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb067_support_mem_0266 f) 0))))
                                      (TAlphaVar.there (show (nb067_alpha_dummy_085) ≠
        (nb067_alpha_dummy_247) from (by
          unfold nb067_alpha_dummy_247;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0268) 0)))) (show (nb067_alpha_dummy_088 f) ≠
        (nb067_alpha_dummy_248 f) from (by
          unfold nb067_alpha_dummy_248;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0269 f) 0)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_085) ≠ (nb067_alpha_dummy_245) from (by
          unfold nb067_alpha_dummy_245;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0265) 0)))) (show (nb067_alpha_dummy_088 f) ≠
        (nb067_alpha_dummy_246 f) from (by
          unfold nb067_alpha_dummy_246;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0267 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb067_alpha_dummy_085))).fv ∪
                                        ((Class.cv (nb067_alpha_dummy_084))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb067_alpha_dummy_088 f))).fv ∪
                                        ((Class.cv (nb067_alpha_dummy_087 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067_split_alpha_0033 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb067_alpha_dummy_085) ≠ (nb067_alpha_dummy_242) from (by
                                        unfold nb067_alpha_dummy_242;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0264)
                                                1)))) (show (nb067_alpha_dummy_088 f) ≠
                                        (nb067_alpha_dummy_244 f) from (by
                                        unfold nb067_alpha_dummy_244;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0266 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb067_alpha_dummy_085) ≠ (nb067_alpha_dummy_241) from
                                        (by
                                          unfold nb067_alpha_dummy_241;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb067_support_mem_0264)
                                                  0)))) (show (nb067_alpha_dummy_088 f) ≠
        (nb067_alpha_dummy_243 f) from (by
                                          unfold nb067_alpha_dummy_243;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb067_support_mem_0266 f) 0))))
                                      (TAlphaVar.there (show (nb067_alpha_dummy_085) ≠
        (nb067_alpha_dummy_247) from (by
          unfold nb067_alpha_dummy_247;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0268) 0)))) (show (nb067_alpha_dummy_088 f) ≠
        (nb067_alpha_dummy_248 f) from (by
          unfold nb067_alpha_dummy_248;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0269 f) 0)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_085) ≠ (nb067_alpha_dummy_245) from (by
          unfold nb067_alpha_dummy_245;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0265) 0)))) (show (nb067_alpha_dummy_088 f) ≠
        (nb067_alpha_dummy_246 f) from (by
          unfold nb067_alpha_dummy_246;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0267 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb067_alpha_dummy_085))).fv ∪
                                        ((Class.cv (nb067_alpha_dummy_084))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb067_alpha_dummy_088 f))).fv ∪
                                        ((Class.cv (nb067_alpha_dummy_087 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067_split_alpha_0033 x y f)))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb067_split_alpha_0036 x y f))))))))
        (TAlphaClass.cv (TAlphaVar.there
            (show (nb067_alpha_dummy_000) ≠ (nb067_alpha_dummy_085) from (by
                unfold nb067_alpha_dummy_085;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0256) 2))))
            (show f ≠ (nb067_alpha_dummy_088 f) from (by
                unfold nb067_alpha_dummy_088;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0258 f) 2))))
            (TAlphaVar.there (show (nb067_alpha_dummy_000) ≠ (nb067_alpha_dummy_084) from (by
                  unfold nb067_alpha_dummy_084;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0256) 1))))
              (show f ≠ (nb067_alpha_dummy_087 f) from (by
                  unfold nb067_alpha_dummy_087;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0258 f) 1))))
              (TAlphaVar.there (show (nb067_alpha_dummy_000) ≠ (nb067_alpha_dummy_083) from (by
                    unfold nb067_alpha_dummy_083;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0256) 0))))
                (show f ≠ (nb067_alpha_dummy_086 f) from (by
                    unfold nb067_alpha_dummy_086;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0258 f) 0))))
                (TAlphaVar.there (show (nb067_alpha_dummy_000) ≠ (nb067_alpha_dummy_089) from
                    (by
                      unfold nb067_alpha_dummy_089;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0257) 0))))
                  (show f ≠ (nb067_alpha_dummy_090 f) from (by
                      unfold nb067_alpha_dummy_090;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0259 f) 0))))
                  (TAlphaVar.there (show (nb067_alpha_dummy_000) ≠ (nb067_alpha_dummy_081) from
                      (by
                        unfold nb067_alpha_dummy_081;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0254) 0))))
                    (show f ≠ (nb067_alpha_dummy_082 f) from (by
                        unfold nb067_alpha_dummy_082;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0255 f) 0)))) (TAlphaVar.there
                      (show (nb067_alpha_dummy_000) ≠ (nb067_alpha_dummy_079) from (by
                          unfold nb067_alpha_dummy_079;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0252) 0))))
                      (show f ≠ (nb067_alpha_dummy_080 f) from (by
                          unfold nb067_alpha_dummy_080;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0253 f) 0))))
                      (TAlphaVar.here _ _ _)))))))))))

theorem nb067_wpp_notmem_0696 : (nb067_alpha_dummy_081) ∉ ((syn_cid)).fv := by
  simpa only [nb067_alpha_dummy_081, fv_syn_cid] using (nb067_compact_fv_empty_0086)

theorem nb067_wpp_notmem_0697 (f : Var) : (nb067_alpha_dummy_082 f) ∉ ((syn_cid)).fv := by
  simpa only [nb067_alpha_dummy_082, fv_syn_cid] using (nb067_compact_fv_empty_0087 f)

theorem nb067_wpp_notmem_0698 : (nb067_alpha_dummy_079) ∉ ((syn_cid)).fv := by
  simpa only [nb067_alpha_dummy_079, fv_syn_cid] using (nb067_compact_fv_empty_0088)

theorem nb067_wpp_notmem_0699 (f : Var) : (nb067_alpha_dummy_080 f) ∉ ((syn_cid)).fv := by
  simpa only [nb067_alpha_dummy_080, fv_syn_cid] using (nb067_compact_fv_empty_0089 f)

theorem nb067_wpp_notmem_0700 : (nb067_alpha_dummy_000) ∉ ((syn_cid)).fv := by
  simpa only [nb067_alpha_dummy_000, fv_syn_cid] using (nb067_compact_fv_empty_0090)

theorem nb067_wpp_notmem_0701 (f : Var) : f ∉ ((syn_cid)).fv := by
  simpa only [fv_syn_cid] using (nb067_compact_fv_empty_0091 f)

theorem nb067_wpp_notmem_0702 : (nb067_alpha_dummy_003) ∉ ((syn_cid)).fv := by
  simpa only [nb067_alpha_dummy_003, fv_syn_cid] using (nb067_compact_fv_empty_0028)

theorem nb067_wpp_notmem_0703 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_004 x y f) ∉ ((syn_cid)).fv := by
  simpa only [nb067_alpha_dummy_004, fv_syn_cid] using (nb067_compact_fv_empty_0029 x y f)

theorem nb067_wpp_notmem_0704 : (nb067_alpha_dummy_002) ∉ ((syn_cid)).fv := by
  simpa only [nb067_alpha_dummy_002, fv_syn_cid] using (nb067_compact_fv_empty_0030)

theorem nb067_wpp_notmem_0705 (y : Var) : y ∉ ((syn_cid)).fv := by
  simpa only [fv_syn_cid] using (nb067_compact_fv_empty_0031 y)

theorem nb067_wpp_notmem_0706 : (nb067_alpha_dummy_001) ∉ ((syn_cid)).fv := by
  simpa only [nb067_alpha_dummy_001, fv_syn_cid] using (nb067_compact_fv_empty_0032)

theorem nb067_wpp_notmem_0707 (x : Var) : x ∉ ((syn_cid)).fv := by
  simpa only [fv_syn_cid] using (nb067_compact_fv_empty_0033 x)

theorem nb067_wpp_notmem_0708 : (nb067_alpha_dummy_005) ∉ ((syn_cid)).fv := by
  simpa only [nb067_alpha_dummy_005, fv_syn_cid] using (nb067_compact_fv_empty_0034)

theorem nb067_wpp_notmem_0709 (x : Var) (y : Var) (f : Var) :
    (nb067_alpha_dummy_006 x y f) ∉ ((syn_cid)).fv := by
  simpa only [nb067_alpha_dummy_006, fv_syn_cid] using (nb067_compact_fv_empty_0035 x y f)

theorem nb067_compact_envfresh_0050 (x : Var) (y : Var) (f : Var) :
    TEnvFresh
      [((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
        ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      ((syn_cid)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb067_alpha_dummy_081) (nb067_alpha_dummy_082 f)
      (nb067_wpp_notmem_0696) (nb067_wpp_notmem_0697 f)
      (TEnvFresh.consFresh (nb067_alpha_dummy_079) (nb067_alpha_dummy_080 f)
        (nb067_wpp_notmem_0698) (nb067_wpp_notmem_0699 f)
        (TEnvFresh.consFresh (nb067_alpha_dummy_000) f (nb067_wpp_notmem_0700)
          (nb067_wpp_notmem_0701 f)
          (TEnvFresh.consFresh (nb067_alpha_dummy_003) (nb067_alpha_dummy_004 x y f)
            (nb067_wpp_notmem_0702) (nb067_wpp_notmem_0703 x y f)
            (TEnvFresh.consFresh (nb067_alpha_dummy_002) y (nb067_wpp_notmem_0704)
              (nb067_wpp_notmem_0705 y)
              (TEnvFresh.consFresh (nb067_alpha_dummy_001) x (nb067_wpp_notmem_0706)
                (nb067_wpp_notmem_0707 x)
                (TEnvFresh.consFresh (nb067_alpha_dummy_005) (nb067_alpha_dummy_006 x y f)
                  (nb067_wpp_notmem_0708) (nb067_wpp_notmem_0709 x y f)
                  (TEnvFresh.nil ((syn_cid)).fv))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
