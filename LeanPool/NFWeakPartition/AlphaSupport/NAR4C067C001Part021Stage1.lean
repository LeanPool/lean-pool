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

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0036`. -/
@[expose]
noncomputable def nb067SplitAlpha0036 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy271), (nb067AlphaDummy272 f)),
        ((nb067AlphaDummy245), (nb067AlphaDummy246 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
        ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
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
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb067AlphaDummy242) ≠
        (nb067AlphaDummy249) from (by
          unfold nb067AlphaDummy249;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0270) 0)))) (show (nb067AlphaDummy244 f) ≠
        (nb067AlphaDummy251 f) from (by
          unfold nb067AlphaDummy251;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0271 f) 0)))) (TAlphaVar.there (show
        (nb067AlphaDummy242) ≠ (nb067AlphaDummy250) from (by
          unfold nb067AlphaDummy250;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0270) 1)))) (show (nb067AlphaDummy244 f) ≠
        (nb067AlphaDummy252 f) from (by
          unfold nb067AlphaDummy252;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0271 f) 1)))) (TAlphaVar.there (show
        (nb067AlphaDummy242) ≠ (nb067AlphaDummy275) from (by
          unfold nb067AlphaDummy275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0300) 0)))) (show (nb067AlphaDummy244 f) ≠
        (nb067AlphaDummy276 f) from (by
          unfold nb067AlphaDummy276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0301 f) 0)))) (TAlphaVar.there (show
        (nb067AlphaDummy242) ≠ (nb067AlphaDummy273) from (by
          unfold nb067AlphaDummy273;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0298) 0)))) (show (nb067AlphaDummy244 f) ≠
        (nb067AlphaDummy274 f) from (by
          unfold nb067AlphaDummy274;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0299 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb067SplitAlpha0035 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb067AlphaDummy242) ≠
        (nb067AlphaDummy249) from (by
          unfold nb067AlphaDummy249;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0270) 0)))) (show (nb067AlphaDummy244 f) ≠
        (nb067AlphaDummy251 f) from (by
          unfold nb067AlphaDummy251;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0271 f) 0)))) (TAlphaVar.there (show
        (nb067AlphaDummy242) ≠ (nb067AlphaDummy250) from (by
          unfold nb067AlphaDummy250;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0270) 1)))) (show (nb067AlphaDummy244 f) ≠
        (nb067AlphaDummy252 f) from (by
          unfold nb067AlphaDummy252;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0271 f) 1)))) (TAlphaVar.there (show
        (nb067AlphaDummy242) ≠ (nb067AlphaDummy275) from (by
          unfold nb067AlphaDummy275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0300) 0)))) (show (nb067AlphaDummy244 f) ≠
        (nb067AlphaDummy276 f) from (by
          unfold nb067AlphaDummy276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0301 f) 0)))) (TAlphaVar.there (show
        (nb067AlphaDummy242) ≠ (nb067AlphaDummy273) from (by
          unfold nb067AlphaDummy273;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0298) 0)))) (show (nb067AlphaDummy244 f) ≠
        (nb067AlphaDummy274 f) from (by
          unfold nb067AlphaDummy274;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0299 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb067SplitAlpha0035 x y f)))))))))
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
                          ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
                          ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
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
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067AlphaDummy242) ≠ (nb067AlphaDummy249) from (by
          unfold nb067AlphaDummy249;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0270) 0)))) (show (nb067AlphaDummy244 f) ≠
        (nb067AlphaDummy251 f) from (by
          unfold nb067AlphaDummy251;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0271 f) 0)))) (TAlphaVar.there (show
        (nb067AlphaDummy242) ≠ (nb067AlphaDummy250) from (by
          unfold nb067AlphaDummy250;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0270) 1)))) (show (nb067AlphaDummy244 f) ≠
        (nb067AlphaDummy252 f) from (by
          unfold nb067AlphaDummy252;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0271 f) 1)))) (TAlphaVar.there (show
        (nb067AlphaDummy242) ≠ (nb067AlphaDummy275) from (by
          unfold nb067AlphaDummy275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0300) 0)))) (show (nb067AlphaDummy244 f) ≠
        (nb067AlphaDummy276 f) from (by
          unfold nb067AlphaDummy276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0301 f)
                  0)))) (TAlphaVar.there (show (nb067AlphaDummy242) ≠ (nb067AlphaDummy273)
        from (by
          unfold nb067AlphaDummy273;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0298)
                  0)))) (show (nb067AlphaDummy244 f) ≠ (nb067AlphaDummy274 f) from (by
          unfold nb067AlphaDummy274;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0299 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb067SplitAlpha0035 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067AlphaDummy242) ≠ (nb067AlphaDummy249) from (by
          unfold nb067AlphaDummy249;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0270) 0)))) (show (nb067AlphaDummy244 f) ≠
        (nb067AlphaDummy251 f) from (by
          unfold nb067AlphaDummy251;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0271 f) 0)))) (TAlphaVar.there (show
        (nb067AlphaDummy242) ≠ (nb067AlphaDummy250) from (by
          unfold nb067AlphaDummy250;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0270) 1)))) (show (nb067AlphaDummy244 f) ≠
        (nb067AlphaDummy252 f) from (by
          unfold nb067AlphaDummy252;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0271 f) 1)))) (TAlphaVar.there (show
        (nb067AlphaDummy242) ≠ (nb067AlphaDummy275) from (by
          unfold nb067AlphaDummy275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0300) 0)))) (show (nb067AlphaDummy244 f) ≠
        (nb067AlphaDummy276 f) from (by
          unfold nb067AlphaDummy276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0301 f)
                  0)))) (TAlphaVar.there (show (nb067AlphaDummy242) ≠ (nb067AlphaDummy273)
        from (by
          unfold nb067AlphaDummy273;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0298)
                  0)))) (show (nb067AlphaDummy244 f) ≠ (nb067AlphaDummy274 f) from (by
          unfold nb067AlphaDummy274;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0299 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb067SplitAlpha0035 x y f)))))))))
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
                            ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
                            ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
                            ((nb067AlphaDummy000), f),
                            ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                            ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                            ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0037`. -/
@[expose]
noncomputable def nb067SplitAlpha0037 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
        ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
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
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067SplitAlpha0016 x y f)))))))))
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
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067SplitAlpha0016 x y f)))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb067SplitAlpha0019 x y f))))))))
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg (nb067SplitAlpha0031 x y f)))))
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
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067SplitAlpha0033 x y f)))))))))
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
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067SplitAlpha0033 x y f)))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb067SplitAlpha0036 x y f))))))))
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
                  (TAlphaVar.there (show (nb067AlphaDummy000) ≠ (nb067AlphaDummy081) from
                      (by
                        unfold nb067AlphaDummy081;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0254) 0))))
                    (show f ≠ (nb067AlphaDummy082 f) from (by
                        unfold nb067AlphaDummy082;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0255 f) 0)))) (TAlphaVar.there
                      (show (nb067AlphaDummy000) ≠ (nb067AlphaDummy079) from (by
                          unfold nb067AlphaDummy079;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0252) 0))))
                      (show f ≠ (nb067AlphaDummy080 f) from (by
                          unfold nb067AlphaDummy080;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0253 f) 0))))
                      (TAlphaVar.here _ _ _)))))))))))

theorem nb067_wpp_notmem_0696 : (nb067AlphaDummy081) ∉ ((synCid)).fv := by
  simpa only [nb067AlphaDummy081, fv_syn_cid] using (nb067_compact_fv_empty_0086)

theorem nb067_wpp_notmem_0697 (f : Var) : (nb067AlphaDummy082 f) ∉ ((synCid)).fv := by
  simpa only [nb067AlphaDummy082, fv_syn_cid] using (nb067_compact_fv_empty_0087 f)

theorem nb067_wpp_notmem_0698 : (nb067AlphaDummy079) ∉ ((synCid)).fv := by
  simpa only [nb067AlphaDummy079, fv_syn_cid] using (nb067_compact_fv_empty_0088)

theorem nb067_wpp_notmem_0699 (f : Var) : (nb067AlphaDummy080 f) ∉ ((synCid)).fv := by
  simpa only [nb067AlphaDummy080, fv_syn_cid] using (nb067_compact_fv_empty_0089 f)

theorem nb067_wpp_notmem_0700 : (nb067AlphaDummy000) ∉ ((synCid)).fv := by
  simpa only [nb067AlphaDummy000, fv_syn_cid] using (nb067_compact_fv_empty_0090)

theorem nb067_wpp_notmem_0701 (f : Var) : f ∉ ((synCid)).fv := by
  simpa only [fv_syn_cid] using (nb067_compact_fv_empty_0091 f)

theorem nb067_wpp_notmem_0702 : (nb067AlphaDummy003) ∉ ((synCid)).fv := by
  simpa only [nb067AlphaDummy003, fv_syn_cid] using (nb067_compact_fv_empty_0028)

theorem nb067_wpp_notmem_0703 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy004 x y f) ∉ ((synCid)).fv := by
  simpa only [nb067AlphaDummy004, fv_syn_cid] using (nb067_compact_fv_empty_0029 x y f)

theorem nb067_wpp_notmem_0704 : (nb067AlphaDummy002) ∉ ((synCid)).fv := by
  simpa only [nb067AlphaDummy002, fv_syn_cid] using (nb067_compact_fv_empty_0030)

theorem nb067_wpp_notmem_0705 (y : Var) : y ∉ ((synCid)).fv := by
  simpa only [fv_syn_cid] using (nb067_compact_fv_empty_0031 y)

theorem nb067_wpp_notmem_0706 : (nb067AlphaDummy001) ∉ ((synCid)).fv := by
  simpa only [nb067AlphaDummy001, fv_syn_cid] using (nb067_compact_fv_empty_0032)

theorem nb067_wpp_notmem_0707 (x : Var) : x ∉ ((synCid)).fv := by
  simpa only [fv_syn_cid] using (nb067_compact_fv_empty_0033 x)

theorem nb067_wpp_notmem_0708 : (nb067AlphaDummy005) ∉ ((synCid)).fv := by
  simpa only [nb067AlphaDummy005, fv_syn_cid] using (nb067_compact_fv_empty_0034)

theorem nb067_wpp_notmem_0709 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy006 x y f) ∉ ((synCid)).fv := by
  simpa only [nb067AlphaDummy006, fv_syn_cid] using (nb067_compact_fv_empty_0035 x y f)

theorem nb067_compact_envfresh_0050 (x : Var) (y : Var) (f : Var) :
    TEnvFresh
      [((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
        ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      ((synCid)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb067AlphaDummy081) (nb067AlphaDummy082 f)
      (nb067_wpp_notmem_0696) (nb067_wpp_notmem_0697 f)
      (TEnvFresh.consFresh (nb067AlphaDummy079) (nb067AlphaDummy080 f)
        (nb067_wpp_notmem_0698) (nb067_wpp_notmem_0699 f)
        (TEnvFresh.consFresh (nb067AlphaDummy000) f (nb067_wpp_notmem_0700)
          (nb067_wpp_notmem_0701 f)
          (TEnvFresh.consFresh (nb067AlphaDummy003) (nb067AlphaDummy004 x y f)
            (nb067_wpp_notmem_0702) (nb067_wpp_notmem_0703 x y f)
            (TEnvFresh.consFresh (nb067AlphaDummy002) y (nb067_wpp_notmem_0704)
              (nb067_wpp_notmem_0705 y)
              (TEnvFresh.consFresh (nb067AlphaDummy001) x (nb067_wpp_notmem_0706)
                (nb067_wpp_notmem_0707 x)
                (TEnvFresh.consFresh (nb067AlphaDummy005) (nb067AlphaDummy006 x y f)
                  (nb067_wpp_notmem_0708) (nb067_wpp_notmem_0709 x y f)
                  (TEnvFresh.nil ((synCid)).fv))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
