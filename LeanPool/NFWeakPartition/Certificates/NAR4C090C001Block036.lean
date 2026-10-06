/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block035

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part102`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0080`. -/
@[expose]
noncomputable def nb090SplitAlpha0080 (v : Var) (u : Var) (A : Class) (h : Var)
    (dv_h_u : h ≠ u) (dv_u_v : u ≠ v) :
    TAlphaWff
      [((nb090AlphaDummy297 A), (nb090AlphaDummy298 u)),
        ((nb090AlphaDummy295 A), (nb090AlphaDummy296 u)),
        ((nb090AlphaDummy283 A), (nb090AlphaDummy284 u)),
        ((nb090AlphaDummy285 A), (nb090AlphaDummy286 u)),
        ((nb090AlphaDummy288 A), (nb090AlphaDummy290 u)),
        ((nb090AlphaDummy287 A), (nb090AlphaDummy289 u)),
        ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy297 A))
          (Class.cab (nb090AlphaDummy291 A)
            (synWrex (nb090AlphaDummy292 A) (Class.cv (nb090AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy291 A))
                (synCphi (Class.cv (nb090AlphaDummy292 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy297 A))
            (Class.cab (nb090AlphaDummy291 A)
              (synWrex (nb090AlphaDummy292 A) (Class.cv (nb090AlphaDummy001 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy291 A))
                  (synCphi (Class.cv (nb090AlphaDummy292 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy298 u))
          (Class.cab (nb090AlphaDummy293 u) (synWrex (nb090AlphaDummy294 u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090AlphaDummy293 u))
                (synCphi (Class.cv (nb090AlphaDummy294 u))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy298 u))
            (Class.cab (nb090AlphaDummy293 u)
              (synWrex (nb090AlphaDummy294 u) (Class.cv u)
                (Wff.classEq (Class.cv (nb090AlphaDummy293 u))
                  (synCphi (Class.cv (nb090AlphaDummy294 u))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy292 A) from (by
                      unfold nb090AlphaDummy292;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0298 A) 1))))
                  (show u ≠ (nb090AlphaDummy294 u) from (by
                      unfold nb090AlphaDummy294;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0300 u) 1))))
                  (TAlphaVar.there
                    (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy291 A) from (by
                        unfold nb090AlphaDummy291;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0298 A) 0))))
                    (show u ≠ (nb090AlphaDummy293 u) from (by
                        unfold nb090AlphaDummy293;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0300 u) 0)))) (TAlphaVar.there
                      (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy297 A) from (by
                          unfold nb090AlphaDummy297;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0302 A) 0))))
                      (show u ≠ (nb090AlphaDummy298 u) from (by
                          unfold nb090AlphaDummy298;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0303 u) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy295 A) from (by
                            unfold nb090AlphaDummy295;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0299 A) 0))))
                        (show u ≠ (nb090AlphaDummy296 u) from (by
                            unfold nb090AlphaDummy296;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0301 u) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy283 A) from (by
                              unfold nb090AlphaDummy283;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0292 A) 0))))
                          (show u ≠ (nb090AlphaDummy284 u) from (by
                              unfold nb090AlphaDummy284;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0295 u) 0))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy285 A) from (by
                                unfold nb090AlphaDummy285;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0293 A) 0))))
                            (show u ≠ (nb090AlphaDummy286 u) from (by
                                unfold nb090AlphaDummy286;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0296 u) 0))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy288 A) from
                                (by
                                  unfold nb090AlphaDummy288;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0294 A) 1))))
                              (show u ≠ (nb090AlphaDummy290 u) from (by
                                  unfold nb090AlphaDummy290;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0297 u) 1))))
                              (TAlphaVar.there (show
                                  (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy287 A) from (by
                                    unfold nb090AlphaDummy287;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0294 A)
                                            0)))) (show u ≠ (nb090AlphaDummy289 u) from (by
                                    unfold nb090AlphaDummy289;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0297 u)
                                            0)))) (TAlphaVar.there (show
                                    (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy041 A) from
                                    (by
                                      unfold nb090AlphaDummy041;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0642 A)
                                              0)))) (show u ≠ (nb090AlphaDummy043 v u h) from
                                    (by
                                      unfold nb090AlphaDummy043;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb090_support_mem_0643 v u h) 0))))
                                  (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
                                    (Ne.symm dv_h_u) (TAlphaVar.there
                                      (freshVar_injective ((A).fv) (by decide)) dv_u_v
                                      (TAlphaVar.here _ _ _)))))))))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090AlphaDummy001 A))).fv ∪
                      ((Class.cv (nb090AlphaDummy283 A))).fv) (by decide))
                  (freshVar_injective
                    (((Class.cv u)).fv ∪ ((Class.cv (nb090AlphaDummy284 u))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090AlphaDummy292 A) ≠ (nb090AlphaDummy299 A) from (by
                              unfold nb090AlphaDummy299;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0304 A) 0))))
                          (show (nb090AlphaDummy294 u) ≠ (nb090AlphaDummy301 u) from (by
                              unfold nb090AlphaDummy301;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0305 u) 0))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy292 A) ≠ (nb090AlphaDummy300 A) from (by
                                unfold nb090AlphaDummy300;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0304 A) 1))))
                            (show (nb090AlphaDummy294 u) ≠ (nb090AlphaDummy302 u) from (by
                                unfold nb090AlphaDummy302;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0305 u) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090AlphaDummy292 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090AlphaDummy294 u))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy299 A) ≠ (nb090AlphaDummy306 A) from (by
          unfold nb090AlphaDummy306;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0308 A) 1)))) (show (nb090AlphaDummy301 u) ≠
        (nb090AlphaDummy309 u) from (by
          unfold nb090AlphaDummy309;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0309 u) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy299 A) ≠ (nb090AlphaDummy305 A) from (by
          unfold nb090AlphaDummy305;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0308 A) 0)))) (show (nb090AlphaDummy301 u) ≠
        (nb090AlphaDummy308 u) from (by
          unfold nb090AlphaDummy308;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0309 u) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy299 A) ≠ (nb090AlphaDummy303 A) from (by
          unfold nb090AlphaDummy303;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0306 A)
                  0)))) (show (nb090AlphaDummy301 u) ≠ (nb090AlphaDummy304 u) from (by
          unfold nb090AlphaDummy304;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0307 u)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy307 A), (nb090AlphaDummy310 u)), ((nb090AlphaDummy306 A),
        (nb090AlphaDummy309 u)), ((nb090AlphaDummy305 A), (nb090AlphaDummy308 u)),
        ((nb090AlphaDummy303 A), (nb090AlphaDummy304 u)), ((nb090AlphaDummy299 A),
        (nb090AlphaDummy301 u)), ((nb090AlphaDummy300 A), (nb090AlphaDummy302 u)),
        ((nb090AlphaDummy292 A), (nb090AlphaDummy294 u)), ((nb090AlphaDummy291 A),
        (nb090AlphaDummy293 u)), ((nb090AlphaDummy297 A), (nb090AlphaDummy298 u)),
        ((nb090AlphaDummy295 A), (nb090AlphaDummy296 u)), ((nb090AlphaDummy283 A),
        (nb090AlphaDummy284 u)), ((nb090AlphaDummy285 A), (nb090AlphaDummy286 u)),
        ((nb090AlphaDummy288 A), (nb090AlphaDummy290 u)), ((nb090AlphaDummy287 A),
        (nb090AlphaDummy289 u)), ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy306
        A) ≠ (nb090AlphaDummy313 A) from (by
          unfold
            nb090AlphaDummy313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0312
                    A)
                  0)))) (show (nb090AlphaDummy309 u) ≠ (nb090AlphaDummy314 u) from (by
          unfold
            nb090AlphaDummy314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0313
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy306 A) ≠
        (nb090AlphaDummy311 A) from (by
          unfold
            nb090AlphaDummy311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0310
                    A)
                  0)))) (show (nb090AlphaDummy309 u) ≠ (nb090AlphaDummy312 u) from (by
          unfold
            nb090AlphaDummy312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0311
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy299
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy301 u))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy307 A) ≠ (nb090AlphaDummy313 A) from (by
          unfold
            nb090AlphaDummy313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0316
                    A)
                  0)))) (show (nb090AlphaDummy310 u) ≠ (nb090AlphaDummy314 u) from (by
          unfold
            nb090AlphaDummy314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0317
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy307 A) ≠
        (nb090AlphaDummy311 A) from (by
          unfold
            nb090AlphaDummy311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0314
                    A)
                  0)))) (show (nb090AlphaDummy310 u) ≠ (nb090AlphaDummy312 u) from (by
          unfold
            nb090AlphaDummy312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0315
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy306 A) ≠ (nb090AlphaDummy313 A) from (by
          unfold
            nb090AlphaDummy313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0312
                    A)
                  0)))) (show (nb090AlphaDummy309 u) ≠ (nb090AlphaDummy314 u) from (by
          unfold
            nb090AlphaDummy314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0313
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy306 A) ≠
        (nb090AlphaDummy311 A) from (by
          unfold
            nb090AlphaDummy311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0310
                    A)
                  0)))) (show (nb090AlphaDummy309 u) ≠ (nb090AlphaDummy312 u) from (by
          unfold
            nb090AlphaDummy312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0311
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy299
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy301 u))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy307 A) ≠ (nb090AlphaDummy313 A) from (by
          unfold
            nb090AlphaDummy313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0316
                    A)
                  0)))) (show (nb090AlphaDummy310 u) ≠ (nb090AlphaDummy314 u) from (by
          unfold
            nb090AlphaDummy314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0317
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy307 A) ≠
        (nb090AlphaDummy311 A) from (by
          unfold
            nb090AlphaDummy311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0314
                    A)
                  0)))) (show (nb090AlphaDummy310 u) ≠ (nb090AlphaDummy312 u) from (by
          unfold
            nb090AlphaDummy312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0315
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy307 A), (nb090AlphaDummy310 u)), ((nb090AlphaDummy306 A),
        (nb090AlphaDummy309 u)), ((nb090AlphaDummy305 A), (nb090AlphaDummy308 u)),
        ((nb090AlphaDummy303 A), (nb090AlphaDummy304 u)), ((nb090AlphaDummy299 A),
        (nb090AlphaDummy301 u)), ((nb090AlphaDummy300 A), (nb090AlphaDummy302 u)),
        ((nb090AlphaDummy292 A), (nb090AlphaDummy294 u)), ((nb090AlphaDummy291 A),
        (nb090AlphaDummy293 u)), ((nb090AlphaDummy297 A), (nb090AlphaDummy298 u)),
        ((nb090AlphaDummy295 A), (nb090AlphaDummy296 u)), ((nb090AlphaDummy283 A),
        (nb090AlphaDummy284 u)), ((nb090AlphaDummy285 A), (nb090AlphaDummy286 u)),
        ((nb090AlphaDummy288 A), (nb090AlphaDummy290 u)), ((nb090AlphaDummy287 A),
        (nb090AlphaDummy289 u)), ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy299 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy301 u))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy299 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy301
        u))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy306 A) ≠ (nb090AlphaDummy317 A) from (by
          unfold
            nb090AlphaDummy317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0320
                    A)
                  0)))) (show (nb090AlphaDummy309 u) ≠ (nb090AlphaDummy318 u) from (by
          unfold
            nb090AlphaDummy318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0321
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy306 A) ≠
        (nb090AlphaDummy315 A) from (by
          unfold
            nb090AlphaDummy315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0318
                    A)
                  0)))) (show (nb090AlphaDummy309 u) ≠ (nb090AlphaDummy316 u) from (by
          unfold
            nb090AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0319
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy299
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy301 u))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy306 A) ≠ (nb090AlphaDummy317 A) from (by
          unfold
            nb090AlphaDummy317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0320
                    A)
                  0)))) (show (nb090AlphaDummy309 u) ≠ (nb090AlphaDummy318 u) from (by
          unfold
            nb090AlphaDummy318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0321
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy306 A) ≠
        (nb090AlphaDummy315 A) from (by
          unfold
            nb090AlphaDummy315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0318
                    A)
                  0)))) (show (nb090AlphaDummy309 u) ≠ (nb090AlphaDummy316 u) from (by
          unfold
            nb090AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0319
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy299
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy301 u))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy307
        A) ≠ (nb090AlphaDummy319 A) from (by
          unfold
            nb090AlphaDummy319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0324
                    A)
                  0)))) (show (nb090AlphaDummy310 u) ≠ (nb090AlphaDummy320 u) from (by
          unfold
            nb090AlphaDummy320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0325
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy307 A) ≠
        (nb090AlphaDummy315 A) from (by
          unfold
            nb090AlphaDummy315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0322
                    A)
                  0)))) (show (nb090AlphaDummy310 u) ≠ (nb090AlphaDummy316 u) from (by
          unfold
            nb090AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0323
                    u)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy307
        A) ≠ (nb090AlphaDummy319 A) from (by
          unfold
            nb090AlphaDummy319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0324
                    A)
                  0)))) (show (nb090AlphaDummy310 u) ≠ (nb090AlphaDummy320 u) from (by
          unfold
            nb090AlphaDummy320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0325
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy307 A) ≠
        (nb090AlphaDummy315 A) from (by
          unfold
            nb090AlphaDummy315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0322
                    A)
                  0)))) (show (nb090AlphaDummy310 u) ≠ (nb090AlphaDummy316 u) from (by
          unfold
            nb090AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0323
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy299 A) ≠ (nb090AlphaDummy303 A) from
                                      (by
                                        unfold nb090AlphaDummy303;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0306 A)
                                                0)))) (show (nb090AlphaDummy301 u) ≠
                                        (nb090AlphaDummy304 u) from (by
                                        unfold nb090AlphaDummy304;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0307 u)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy303 A), (nb090AlphaDummy304 u)),
                                    ((nb090AlphaDummy299 A), (nb090AlphaDummy301 u)),
                                    ((nb090AlphaDummy300 A), (nb090AlphaDummy302 u)),
                                    ((nb090AlphaDummy292 A), (nb090AlphaDummy294 u)),
                                    ((nb090AlphaDummy291 A), (nb090AlphaDummy293 u)),
                                    ((nb090AlphaDummy297 A), (nb090AlphaDummy298 u)),
                                    ((nb090AlphaDummy295 A), (nb090AlphaDummy296 u)),
                                    ((nb090AlphaDummy283 A), (nb090AlphaDummy284 u)),
                                    ((nb090AlphaDummy285 A), (nb090AlphaDummy286 u)),
                                    ((nb090AlphaDummy288 A), (nb090AlphaDummy290 u)),
                                    ((nb090AlphaDummy287 A), (nb090AlphaDummy289 u)),
                                    ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy299 A) ≠ (nb090AlphaDummy303 A) from
                                    (by
                                      unfold nb090AlphaDummy303;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0306 A)
                                              0)))) (show
                                    (nb090AlphaDummy301 u) ≠ (nb090AlphaDummy304 u) from
                                    (by
                                      unfold nb090AlphaDummy304;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0307 u)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy299 A) ≠ (nb090AlphaDummy303 A) from
                                      (by
                                        unfold nb090AlphaDummy303;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0306 A)
                                                0)))) (show (nb090AlphaDummy301 u) ≠
                                        (nb090AlphaDummy304 u) from (by
                                        unfold nb090AlphaDummy304;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0307 u)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy303 A), (nb090AlphaDummy304 u)),
                                    ((nb090AlphaDummy299 A), (nb090AlphaDummy301 u)),
                                    ((nb090AlphaDummy300 A), (nb090AlphaDummy302 u)),
                                    ((nb090AlphaDummy292 A), (nb090AlphaDummy294 u)),
                                    ((nb090AlphaDummy291 A), (nb090AlphaDummy293 u)),
                                    ((nb090AlphaDummy297 A), (nb090AlphaDummy298 u)),
                                    ((nb090AlphaDummy295 A), (nb090AlphaDummy296 u)),
                                    ((nb090AlphaDummy283 A), (nb090AlphaDummy284 u)),
                                    ((nb090AlphaDummy285 A), (nb090AlphaDummy286 u)),
                                    ((nb090AlphaDummy288 A), (nb090AlphaDummy290 u)),
                                    ((nb090AlphaDummy287 A), (nb090AlphaDummy289 u)),
                                    ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy292 A) from (by
                        unfold nb090AlphaDummy292;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0298 A) 1))))
                    (show u ≠ (nb090AlphaDummy294 u) from (by
                        unfold nb090AlphaDummy294;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0300 u) 1)))) (TAlphaVar.there
                      (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy291 A) from (by
                          unfold nb090AlphaDummy291;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0298 A) 0))))
                      (show u ≠ (nb090AlphaDummy293 u) from (by
                          unfold nb090AlphaDummy293;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0300 u) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy297 A) from (by
                            unfold nb090AlphaDummy297;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0302 A) 0))))
                        (show u ≠ (nb090AlphaDummy298 u) from (by
                            unfold nb090AlphaDummy298;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0303 u) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy295 A) from (by
                              unfold nb090AlphaDummy295;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0299 A) 0))))
                          (show u ≠ (nb090AlphaDummy296 u) from (by
                              unfold nb090AlphaDummy296;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0301 u) 0))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy283 A) from (by
                                unfold nb090AlphaDummy283;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0292 A) 0))))
                            (show u ≠ (nb090AlphaDummy284 u) from (by
                                unfold nb090AlphaDummy284;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0295 u) 0))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy285 A) from
                                (by
                                  unfold nb090AlphaDummy285;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0293 A) 0))))
                              (show u ≠ (nb090AlphaDummy286 u) from (by
                                  unfold nb090AlphaDummy286;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0296 u) 0))))
                              (TAlphaVar.there (show
                                  (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy288 A) from (by
                                    unfold nb090AlphaDummy288;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0294 A)
                                            1)))) (show u ≠ (nb090AlphaDummy290 u) from (by
                                    unfold nb090AlphaDummy290;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0297 u)
                                            1)))) (TAlphaVar.there (show
                                    (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy287 A) from
                                    (by
                                      unfold nb090AlphaDummy287;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0294 A)
                                              0)))) (show u ≠ (nb090AlphaDummy289 u) from (by
                                      unfold nb090AlphaDummy289;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0297 u)
                                              0)))) (TAlphaVar.there (show
                                      (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy041 A) from
                                      (by
                                        unfold nb090AlphaDummy041;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0642 A)
                                                0))))
                                    (show u ≠ (nb090AlphaDummy043 v u h) from (by
                                        unfold nb090AlphaDummy043;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0643 v u h) 0))))
                                    (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
                                      (Ne.symm dv_h_u) (TAlphaVar.there
                                        (freshVar_injective ((A).fv) (by decide)) dv_u_v
                                        (TAlphaVar.here _ _ _)))))))))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090AlphaDummy001 A))).fv ∪
                        ((Class.cv (nb090AlphaDummy283 A))).fv) (by decide))
                    (freshVar_injective
                      (((Class.cv u)).fv ∪ ((Class.cv (nb090AlphaDummy284 u))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy292 A) ≠ (nb090AlphaDummy299 A) from (by
                                unfold nb090AlphaDummy299;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0304 A) 0))))
                            (show (nb090AlphaDummy294 u) ≠ (nb090AlphaDummy301 u) from (by
                                unfold nb090AlphaDummy301;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0305 u) 0))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy292 A) ≠ (nb090AlphaDummy300 A) from
                                (by
                                  unfold nb090AlphaDummy300;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0304 A) 1))))
                              (show (nb090AlphaDummy294 u) ≠ (nb090AlphaDummy302 u) from
                                (by
                                  unfold nb090AlphaDummy302;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0305 u) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090AlphaDummy292 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090AlphaDummy294 u))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy299 A) ≠ (nb090AlphaDummy306 A) from (by
          unfold nb090AlphaDummy306;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0308 A) 1)))) (show (nb090AlphaDummy301 u) ≠
        (nb090AlphaDummy309 u) from (by
          unfold nb090AlphaDummy309;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0309 u) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy299 A) ≠ (nb090AlphaDummy305 A) from (by
          unfold nb090AlphaDummy305;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0308 A)
                  0)))) (show (nb090AlphaDummy301 u) ≠ (nb090AlphaDummy308 u) from (by
          unfold nb090AlphaDummy308;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0309 u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy299 A) ≠
        (nb090AlphaDummy303 A) from (by
          unfold nb090AlphaDummy303;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0306 A)
                  0)))) (show (nb090AlphaDummy301 u) ≠ (nb090AlphaDummy304 u) from (by
          unfold nb090AlphaDummy304;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0307 u)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy307 A), (nb090AlphaDummy310 u)), ((nb090AlphaDummy306 A),
        (nb090AlphaDummy309 u)), ((nb090AlphaDummy305 A), (nb090AlphaDummy308 u)),
        ((nb090AlphaDummy303 A), (nb090AlphaDummy304 u)), ((nb090AlphaDummy299 A),
        (nb090AlphaDummy301 u)), ((nb090AlphaDummy300 A), (nb090AlphaDummy302 u)),
        ((nb090AlphaDummy292 A), (nb090AlphaDummy294 u)), ((nb090AlphaDummy291 A),
        (nb090AlphaDummy293 u)), ((nb090AlphaDummy297 A), (nb090AlphaDummy298 u)),
        ((nb090AlphaDummy295 A), (nb090AlphaDummy296 u)), ((nb090AlphaDummy283 A),
        (nb090AlphaDummy284 u)), ((nb090AlphaDummy285 A), (nb090AlphaDummy286 u)),
        ((nb090AlphaDummy288 A), (nb090AlphaDummy290 u)), ((nb090AlphaDummy287 A),
        (nb090AlphaDummy289 u)), ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy306
        A) ≠ (nb090AlphaDummy313 A) from (by
          unfold
            nb090AlphaDummy313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0312
                    A)
                  0)))) (show (nb090AlphaDummy309 u) ≠ (nb090AlphaDummy314 u) from (by
          unfold
            nb090AlphaDummy314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0313
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy306 A) ≠
        (nb090AlphaDummy311 A) from (by
          unfold
            nb090AlphaDummy311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0310
                    A)
                  0)))) (show (nb090AlphaDummy309 u) ≠ (nb090AlphaDummy312 u) from (by
          unfold
            nb090AlphaDummy312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0311
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy299
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy301 u))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy307 A) ≠ (nb090AlphaDummy313 A) from (by
          unfold
            nb090AlphaDummy313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0316
                    A)
                  0)))) (show (nb090AlphaDummy310 u) ≠ (nb090AlphaDummy314 u) from (by
          unfold
            nb090AlphaDummy314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0317
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy307 A) ≠
        (nb090AlphaDummy311 A) from (by
          unfold
            nb090AlphaDummy311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0314
                    A)
                  0)))) (show (nb090AlphaDummy310 u) ≠ (nb090AlphaDummy312 u) from (by
          unfold
            nb090AlphaDummy312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0315
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy306 A) ≠ (nb090AlphaDummy313 A) from (by
          unfold
            nb090AlphaDummy313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0312
                    A)
                  0)))) (show (nb090AlphaDummy309 u) ≠ (nb090AlphaDummy314 u) from (by
          unfold
            nb090AlphaDummy314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0313
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy306 A) ≠
        (nb090AlphaDummy311 A) from (by
          unfold
            nb090AlphaDummy311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0310
                    A)
                  0)))) (show (nb090AlphaDummy309 u) ≠ (nb090AlphaDummy312 u) from (by
          unfold
            nb090AlphaDummy312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0311
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy299
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy301 u))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy307 A) ≠ (nb090AlphaDummy313 A) from (by
          unfold
            nb090AlphaDummy313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0316
                    A)
                  0)))) (show (nb090AlphaDummy310 u) ≠ (nb090AlphaDummy314 u) from (by
          unfold
            nb090AlphaDummy314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0317
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy307 A) ≠
        (nb090AlphaDummy311 A) from (by
          unfold
            nb090AlphaDummy311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0314
                    A)
                  0)))) (show (nb090AlphaDummy310 u) ≠ (nb090AlphaDummy312 u) from (by
          unfold
            nb090AlphaDummy312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0315
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy307 A), (nb090AlphaDummy310 u)), ((nb090AlphaDummy306 A),
        (nb090AlphaDummy309 u)), ((nb090AlphaDummy305 A), (nb090AlphaDummy308 u)),
        ((nb090AlphaDummy303 A), (nb090AlphaDummy304 u)), ((nb090AlphaDummy299 A),
        (nb090AlphaDummy301 u)), ((nb090AlphaDummy300 A), (nb090AlphaDummy302 u)),
        ((nb090AlphaDummy292 A), (nb090AlphaDummy294 u)), ((nb090AlphaDummy291 A),
        (nb090AlphaDummy293 u)), ((nb090AlphaDummy297 A), (nb090AlphaDummy298 u)),
        ((nb090AlphaDummy295 A), (nb090AlphaDummy296 u)), ((nb090AlphaDummy283 A),
        (nb090AlphaDummy284 u)), ((nb090AlphaDummy285 A), (nb090AlphaDummy286 u)),
        ((nb090AlphaDummy288 A), (nb090AlphaDummy290 u)), ((nb090AlphaDummy287 A),
        (nb090AlphaDummy289 u)), ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy299 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy301 u))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy299 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy301
        u))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy306 A) ≠ (nb090AlphaDummy317 A) from (by
          unfold
            nb090AlphaDummy317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0320
                    A)
                  0)))) (show (nb090AlphaDummy309 u) ≠ (nb090AlphaDummy318 u) from (by
          unfold
            nb090AlphaDummy318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0321
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy306 A) ≠
        (nb090AlphaDummy315 A) from (by
          unfold
            nb090AlphaDummy315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0318
                    A)
                  0)))) (show (nb090AlphaDummy309 u) ≠ (nb090AlphaDummy316 u) from (by
          unfold
            nb090AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0319
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy299
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy301 u))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy306 A) ≠ (nb090AlphaDummy317 A) from (by
          unfold
            nb090AlphaDummy317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0320
                    A)
                  0)))) (show (nb090AlphaDummy309 u) ≠ (nb090AlphaDummy318 u) from (by
          unfold
            nb090AlphaDummy318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0321
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy306 A) ≠
        (nb090AlphaDummy315 A) from (by
          unfold
            nb090AlphaDummy315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0318
                    A)
                  0)))) (show (nb090AlphaDummy309 u) ≠ (nb090AlphaDummy316 u) from (by
          unfold
            nb090AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0319
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy299
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy301 u))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy307
        A) ≠ (nb090AlphaDummy319 A) from (by
          unfold
            nb090AlphaDummy319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0324
                    A)
                  0)))) (show (nb090AlphaDummy310 u) ≠ (nb090AlphaDummy320 u) from (by
          unfold
            nb090AlphaDummy320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0325
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy307 A) ≠
        (nb090AlphaDummy315 A) from (by
          unfold
            nb090AlphaDummy315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0322
                    A)
                  0)))) (show (nb090AlphaDummy310 u) ≠ (nb090AlphaDummy316 u) from (by
          unfold
            nb090AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0323
                    u)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy307
        A) ≠ (nb090AlphaDummy319 A) from (by
          unfold
            nb090AlphaDummy319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0324
                    A)
                  0)))) (show (nb090AlphaDummy310 u) ≠ (nb090AlphaDummy320 u) from (by
          unfold
            nb090AlphaDummy320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0325
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy307 A) ≠
        (nb090AlphaDummy315 A) from (by
          unfold
            nb090AlphaDummy315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0322
                    A)
                  0)))) (show (nb090AlphaDummy310 u) ≠ (nb090AlphaDummy316 u) from (by
          unfold
            nb090AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0323
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy299 A) ≠ (nb090AlphaDummy303 A)
                                        from (by
                                          unfold nb090AlphaDummy303;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0306 A) 0)))) (show
                                        (nb090AlphaDummy301 u) ≠ (nb090AlphaDummy304 u)
                                        from (by
                                          unfold nb090AlphaDummy304;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0307 u) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy303 A), (nb090AlphaDummy304 u)),
                                      ((nb090AlphaDummy299 A), (nb090AlphaDummy301 u)),
                                      ((nb090AlphaDummy300 A), (nb090AlphaDummy302 u)),
                                      ((nb090AlphaDummy292 A), (nb090AlphaDummy294 u)),
                                      ((nb090AlphaDummy291 A), (nb090AlphaDummy293 u)),
                                      ((nb090AlphaDummy297 A), (nb090AlphaDummy298 u)),
                                      ((nb090AlphaDummy295 A), (nb090AlphaDummy296 u)),
                                      ((nb090AlphaDummy283 A), (nb090AlphaDummy284 u)),
                                      ((nb090AlphaDummy285 A), (nb090AlphaDummy286 u)),
                                      ((nb090AlphaDummy288 A), (nb090AlphaDummy290 u)),
                                      ((nb090AlphaDummy287 A), (nb090AlphaDummy289 u)),
                                      ((nb090AlphaDummy041 A),
                                        (nb090AlphaDummy043 v u h)),
                                      ((nb090AlphaDummy000 A), h),
                                      ((nb090AlphaDummy002 A), v),
                                      ((nb090AlphaDummy001 A), u),
                                      ((nb090AlphaDummy003 A),
                                        (nb090AlphaDummy004 v u A h))]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy299 A) ≠ (nb090AlphaDummy303 A) from
                                      (by
                                        unfold nb090AlphaDummy303;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0306 A)
                                                0)))) (show (nb090AlphaDummy301 u) ≠
                                        (nb090AlphaDummy304 u) from (by
                                        unfold nb090AlphaDummy304;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0307 u)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy299 A) ≠ (nb090AlphaDummy303 A)
                                        from (by
                                          unfold nb090AlphaDummy303;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0306 A) 0)))) (show
                                        (nb090AlphaDummy301 u) ≠ (nb090AlphaDummy304 u)
                                        from (by
                                          unfold nb090AlphaDummy304;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0307 u) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy303 A), (nb090AlphaDummy304 u)),
                                      ((nb090AlphaDummy299 A), (nb090AlphaDummy301 u)),
                                      ((nb090AlphaDummy300 A), (nb090AlphaDummy302 u)),
                                      ((nb090AlphaDummy292 A), (nb090AlphaDummy294 u)),
                                      ((nb090AlphaDummy291 A), (nb090AlphaDummy293 u)),
                                      ((nb090AlphaDummy297 A), (nb090AlphaDummy298 u)),
                                      ((nb090AlphaDummy295 A), (nb090AlphaDummy296 u)),
                                      ((nb090AlphaDummy283 A), (nb090AlphaDummy284 u)),
                                      ((nb090AlphaDummy285 A), (nb090AlphaDummy286 u)),
                                      ((nb090AlphaDummy288 A), (nb090AlphaDummy290 u)),
                                      ((nb090AlphaDummy287 A), (nb090AlphaDummy289 u)),
                                      ((nb090AlphaDummy041 A),
                                        (nb090AlphaDummy043 v u h)),
                                      ((nb090AlphaDummy000 A), h),
                                      ((nb090AlphaDummy002 A), v),
                                      ((nb090AlphaDummy001 A), u),
                                      ((nb090AlphaDummy003 A),
                                        (nb090AlphaDummy004 v u A h))] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part103`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0081`. -/
@[expose]
noncomputable def nb090SplitAlpha0081 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy323 A), (nb090AlphaDummy324 u)),
        ((nb090AlphaDummy292 A), (nb090AlphaDummy294 u)),
        ((nb090AlphaDummy291 A), (nb090AlphaDummy293 u)),
        ((nb090AlphaDummy321 A), (nb090AlphaDummy322 u)),
        ((nb090AlphaDummy295 A), (nb090AlphaDummy296 u)),
        ((nb090AlphaDummy283 A), (nb090AlphaDummy284 u)),
        ((nb090AlphaDummy285 A), (nb090AlphaDummy286 u)),
        ((nb090AlphaDummy288 A), (nb090AlphaDummy290 u)),
        ((nb090AlphaDummy287 A), (nb090AlphaDummy289 u)),
        ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.classMem (Class.cv (nb090AlphaDummy323 A))
        (synCcompl (synCphi (Class.cv (nb090AlphaDummy292 A)))))
      (Wff.classMem (Class.cv (nb090AlphaDummy324 u))
        (synCcompl (synCphi (Class.cv (nb090AlphaDummy294 u))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb090AlphaDummy292 A) ≠ (nb090AlphaDummy299 A) from (by
                            unfold nb090AlphaDummy299;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0304 A) 0))))
                        (show (nb090AlphaDummy294 u) ≠ (nb090AlphaDummy301 u) from (by
                            unfold nb090AlphaDummy301;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0305 u) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy292 A) ≠ (nb090AlphaDummy300 A) from (by
                              unfold nb090AlphaDummy300;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0304 A) 1))))
                          (show (nb090AlphaDummy294 u) ≠ (nb090AlphaDummy302 u) from (by
                              unfold nb090AlphaDummy302;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0305 u) 1))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy292 A) ≠ (nb090AlphaDummy325 A) from (by
                                unfold nb090AlphaDummy325;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0334 A) 0))))
                            (show (nb090AlphaDummy294 u) ≠ (nb090AlphaDummy326 u) from (by
                                unfold nb090AlphaDummy326;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0335 u) 0))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy292 A) ≠ (nb090AlphaDummy323 A) from
                                (by
                                  unfold nb090AlphaDummy323;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0332 A) 0))))
                              (show (nb090AlphaDummy294 u) ≠ (nb090AlphaDummy324 u) from
                                (by
                                  unfold nb090AlphaDummy324;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0333 u) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there
                        (freshVar_injective (((Class.cv (nb090AlphaDummy292 A))).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv (nb090AlphaDummy294 u))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb090AlphaDummy299 A) ≠
        (nb090AlphaDummy306 A) from (by
          unfold nb090AlphaDummy306;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0308 A) 1)))) (show (nb090AlphaDummy301 u) ≠
        (nb090AlphaDummy309 u) from (by
          unfold nb090AlphaDummy309;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0309 u) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy299 A) ≠ (nb090AlphaDummy305 A) from (by
          unfold nb090AlphaDummy305;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0308 A) 0)))) (show (nb090AlphaDummy301 u) ≠
        (nb090AlphaDummy308 u) from (by
          unfold nb090AlphaDummy308;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0309 u) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy299 A) ≠ (nb090AlphaDummy303 A) from (by
          unfold nb090AlphaDummy303;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0306 A) 0)))) (show (nb090AlphaDummy301 u) ≠
        (nb090AlphaDummy304 u) from (by
          unfold nb090AlphaDummy304;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0307 u) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy307 A), (nb090AlphaDummy310 u)), ((nb090AlphaDummy306 A),
        (nb090AlphaDummy309 u)), ((nb090AlphaDummy305 A), (nb090AlphaDummy308 u)),
        ((nb090AlphaDummy303 A), (nb090AlphaDummy304 u)), ((nb090AlphaDummy299 A),
        (nb090AlphaDummy301 u)), ((nb090AlphaDummy300 A), (nb090AlphaDummy302 u)),
        ((nb090AlphaDummy325 A), (nb090AlphaDummy326 u)), ((nb090AlphaDummy323 A),
        (nb090AlphaDummy324 u)), ((nb090AlphaDummy292 A), (nb090AlphaDummy294 u)),
        ((nb090AlphaDummy291 A), (nb090AlphaDummy293 u)), ((nb090AlphaDummy321 A),
        (nb090AlphaDummy322 u)), ((nb090AlphaDummy295 A), (nb090AlphaDummy296 u)),
        ((nb090AlphaDummy283 A), (nb090AlphaDummy284 u)), ((nb090AlphaDummy285 A),
        (nb090AlphaDummy286 u)), ((nb090AlphaDummy288 A), (nb090AlphaDummy290 u)),
        ((nb090AlphaDummy287 A), (nb090AlphaDummy289 u)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy306 A) ≠ (nb090AlphaDummy313 A) from (by
          unfold
            nb090AlphaDummy313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0312
                    A)
                  0)))) (show (nb090AlphaDummy309 u) ≠ (nb090AlphaDummy314 u) from (by
          unfold
            nb090AlphaDummy314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0313
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy306 A) ≠
        (nb090AlphaDummy311 A) from (by
          unfold
            nb090AlphaDummy311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0310
                    A)
                  0)))) (show (nb090AlphaDummy309 u) ≠ (nb090AlphaDummy312 u) from (by
          unfold
            nb090AlphaDummy312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0311
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy299
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy301 u))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy307 A) ≠ (nb090AlphaDummy313 A) from (by
          unfold
            nb090AlphaDummy313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0316
                    A)
                  0)))) (show (nb090AlphaDummy310 u) ≠ (nb090AlphaDummy314 u) from (by
          unfold
            nb090AlphaDummy314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0317
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy307 A) ≠
        (nb090AlphaDummy311 A) from (by
          unfold
            nb090AlphaDummy311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0314
                    A)
                  0)))) (show (nb090AlphaDummy310 u) ≠ (nb090AlphaDummy312 u) from (by
          unfold
            nb090AlphaDummy312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0315
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy306 A) ≠ (nb090AlphaDummy313 A) from (by
          unfold
            nb090AlphaDummy313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0312
                    A)
                  0)))) (show (nb090AlphaDummy309 u) ≠ (nb090AlphaDummy314 u) from (by
          unfold
            nb090AlphaDummy314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0313
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy306 A) ≠
        (nb090AlphaDummy311 A) from (by
          unfold
            nb090AlphaDummy311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0310
                    A)
                  0)))) (show (nb090AlphaDummy309 u) ≠ (nb090AlphaDummy312 u) from (by
          unfold
            nb090AlphaDummy312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0311
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy299
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy301 u))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy307 A) ≠ (nb090AlphaDummy313 A) from (by
          unfold
            nb090AlphaDummy313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0316
                    A)
                  0)))) (show (nb090AlphaDummy310 u) ≠ (nb090AlphaDummy314 u) from (by
          unfold
            nb090AlphaDummy314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0317
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy307 A) ≠
        (nb090AlphaDummy311 A) from (by
          unfold
            nb090AlphaDummy311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0314
                    A)
                  0)))) (show (nb090AlphaDummy310 u) ≠ (nb090AlphaDummy312 u) from (by
          unfold
            nb090AlphaDummy312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0315
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy307 A), (nb090AlphaDummy310 u)), ((nb090AlphaDummy306 A),
        (nb090AlphaDummy309 u)), ((nb090AlphaDummy305 A), (nb090AlphaDummy308 u)),
        ((nb090AlphaDummy303 A), (nb090AlphaDummy304 u)), ((nb090AlphaDummy299 A),
        (nb090AlphaDummy301 u)), ((nb090AlphaDummy300 A), (nb090AlphaDummy302 u)),
        ((nb090AlphaDummy325 A), (nb090AlphaDummy326 u)), ((nb090AlphaDummy323 A),
        (nb090AlphaDummy324 u)), ((nb090AlphaDummy292 A), (nb090AlphaDummy294 u)),
        ((nb090AlphaDummy291 A), (nb090AlphaDummy293 u)), ((nb090AlphaDummy321 A),
        (nb090AlphaDummy322 u)), ((nb090AlphaDummy295 A), (nb090AlphaDummy296 u)),
        ((nb090AlphaDummy283 A), (nb090AlphaDummy284 u)), ((nb090AlphaDummy285 A),
        (nb090AlphaDummy286 u)), ((nb090AlphaDummy288 A), (nb090AlphaDummy290 u)),
        ((nb090AlphaDummy287 A), (nb090AlphaDummy289 u)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy299 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy301 u))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy299 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy301 u))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy306
        A) ≠ (nb090AlphaDummy317 A) from (by
          unfold
            nb090AlphaDummy317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0320
                    A)
                  0)))) (show (nb090AlphaDummy309 u) ≠ (nb090AlphaDummy318 u) from (by
          unfold
            nb090AlphaDummy318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0321
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy306 A) ≠
        (nb090AlphaDummy315 A) from (by
          unfold
            nb090AlphaDummy315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0318
                    A)
                  0)))) (show (nb090AlphaDummy309 u) ≠ (nb090AlphaDummy316 u) from (by
          unfold
            nb090AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0319
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy299
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy301 u))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy306 A) ≠ (nb090AlphaDummy317 A) from (by
          unfold
            nb090AlphaDummy317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0320
                    A)
                  0)))) (show (nb090AlphaDummy309 u) ≠ (nb090AlphaDummy318 u) from (by
          unfold
            nb090AlphaDummy318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0321
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy306 A) ≠
        (nb090AlphaDummy315 A) from (by
          unfold
            nb090AlphaDummy315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0318
                    A)
                  0)))) (show (nb090AlphaDummy309 u) ≠ (nb090AlphaDummy316 u) from (by
          unfold
            nb090AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0319
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy299
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy301 u))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy307
        A) ≠ (nb090AlphaDummy319 A) from (by
          unfold
            nb090AlphaDummy319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0324
                    A)
                  0)))) (show (nb090AlphaDummy310 u) ≠ (nb090AlphaDummy320 u) from (by
          unfold
            nb090AlphaDummy320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0325
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy307 A) ≠
        (nb090AlphaDummy315 A) from (by
          unfold
            nb090AlphaDummy315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0322
                    A)
                  0)))) (show (nb090AlphaDummy310 u) ≠ (nb090AlphaDummy316 u) from (by
          unfold
            nb090AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0323
                    u)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy307
        A) ≠ (nb090AlphaDummy319 A) from (by
          unfold
            nb090AlphaDummy319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0324
                    A)
                  0)))) (show (nb090AlphaDummy310 u) ≠ (nb090AlphaDummy320 u) from (by
          unfold
            nb090AlphaDummy320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0325
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy307 A) ≠
        (nb090AlphaDummy315 A) from (by
          unfold
            nb090AlphaDummy315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0322
                    A)
                  0)))) (show (nb090AlphaDummy310 u) ≠ (nb090AlphaDummy316 u) from (by
          unfold
            nb090AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0323
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy299 A) ≠ (nb090AlphaDummy303 A) from
                                    (by
                                      unfold nb090AlphaDummy303;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0306 A)
                                              0)))) (show
                                    (nb090AlphaDummy301 u) ≠ (nb090AlphaDummy304 u) from
                                    (by
                                      unfold nb090AlphaDummy304;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0307 u)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed
                                [((nb090AlphaDummy303 A), (nb090AlphaDummy304 u)),
                                  ((nb090AlphaDummy299 A), (nb090AlphaDummy301 u)),
                                  ((nb090AlphaDummy300 A), (nb090AlphaDummy302 u)),
                                  ((nb090AlphaDummy325 A), (nb090AlphaDummy326 u)),
                                  ((nb090AlphaDummy323 A), (nb090AlphaDummy324 u)),
                                  ((nb090AlphaDummy292 A), (nb090AlphaDummy294 u)),
                                  ((nb090AlphaDummy291 A), (nb090AlphaDummy293 u)),
                                  ((nb090AlphaDummy321 A), (nb090AlphaDummy322 u)),
                                  ((nb090AlphaDummy295 A), (nb090AlphaDummy296 u)),
                                  ((nb090AlphaDummy283 A), (nb090AlphaDummy284 u)),
                                  ((nb090AlphaDummy285 A), (nb090AlphaDummy286 u)),
                                  ((nb090AlphaDummy288 A), (nb090AlphaDummy290 u)),
                                  ((nb090AlphaDummy287 A), (nb090AlphaDummy289 u)),
                                  ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
                                  ((nb090AlphaDummy000 A), h),
                                  ((nb090AlphaDummy002 A), v),
                                  ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                    (nb090AlphaDummy004 v u A h))]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb090AlphaDummy299 A) ≠ (nb090AlphaDummy303 A) from (by
                                    unfold nb090AlphaDummy303;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0306 A)
                                            0)))) (show
                                  (nb090AlphaDummy301 u) ≠ (nb090AlphaDummy304 u) from (by
                                    unfold nb090AlphaDummy304;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0307 u)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy299 A) ≠ (nb090AlphaDummy303 A) from
                                    (by
                                      unfold nb090AlphaDummy303;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0306 A)
                                              0)))) (show
                                    (nb090AlphaDummy301 u) ≠ (nb090AlphaDummy304 u) from
                                    (by
                                      unfold nb090AlphaDummy304;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0307 u)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed
                                [((nb090AlphaDummy303 A), (nb090AlphaDummy304 u)),
                                  ((nb090AlphaDummy299 A), (nb090AlphaDummy301 u)),
                                  ((nb090AlphaDummy300 A), (nb090AlphaDummy302 u)),
                                  ((nb090AlphaDummy325 A), (nb090AlphaDummy326 u)),
                                  ((nb090AlphaDummy323 A), (nb090AlphaDummy324 u)),
                                  ((nb090AlphaDummy292 A), (nb090AlphaDummy294 u)),
                                  ((nb090AlphaDummy291 A), (nb090AlphaDummy293 u)),
                                  ((nb090AlphaDummy321 A), (nb090AlphaDummy322 u)),
                                  ((nb090AlphaDummy295 A), (nb090AlphaDummy296 u)),
                                  ((nb090AlphaDummy283 A), (nb090AlphaDummy284 u)),
                                  ((nb090AlphaDummy285 A), (nb090AlphaDummy286 u)),
                                  ((nb090AlphaDummy288 A), (nb090AlphaDummy290 u)),
                                  ((nb090AlphaDummy287 A), (nb090AlphaDummy289 u)),
                                  ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
                                  ((nb090AlphaDummy000 A), h),
                                  ((nb090AlphaDummy002 A), v),
                                  ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                    (nb090AlphaDummy004 v u A h))]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb090AlphaDummy292 A) ≠ (nb090AlphaDummy299 A) from (by
                            unfold nb090AlphaDummy299;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0304 A) 0))))
                        (show (nb090AlphaDummy294 u) ≠ (nb090AlphaDummy301 u) from (by
                            unfold nb090AlphaDummy301;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0305 u) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy292 A) ≠ (nb090AlphaDummy300 A) from (by
                              unfold nb090AlphaDummy300;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0304 A) 1))))
                          (show (nb090AlphaDummy294 u) ≠ (nb090AlphaDummy302 u) from (by
                              unfold nb090AlphaDummy302;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0305 u) 1))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy292 A) ≠ (nb090AlphaDummy325 A) from (by
                                unfold nb090AlphaDummy325;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0334 A) 0))))
                            (show (nb090AlphaDummy294 u) ≠ (nb090AlphaDummy326 u) from (by
                                unfold nb090AlphaDummy326;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0335 u) 0))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy292 A) ≠ (nb090AlphaDummy323 A) from
                                (by
                                  unfold nb090AlphaDummy323;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0332 A) 0))))
                              (show (nb090AlphaDummy294 u) ≠ (nb090AlphaDummy324 u) from
                                (by
                                  unfold nb090AlphaDummy324;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0333 u) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there
                        (freshVar_injective (((Class.cv (nb090AlphaDummy292 A))).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv (nb090AlphaDummy294 u))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb090AlphaDummy299 A) ≠
        (nb090AlphaDummy306 A) from (by
          unfold nb090AlphaDummy306;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0308 A) 1)))) (show (nb090AlphaDummy301 u) ≠
        (nb090AlphaDummy309 u) from (by
          unfold nb090AlphaDummy309;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0309 u) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy299 A) ≠ (nb090AlphaDummy305 A) from (by
          unfold nb090AlphaDummy305;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0308 A) 0)))) (show (nb090AlphaDummy301 u) ≠
        (nb090AlphaDummy308 u) from (by
          unfold nb090AlphaDummy308;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0309 u) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy299 A) ≠ (nb090AlphaDummy303 A) from (by
          unfold nb090AlphaDummy303;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0306 A) 0)))) (show (nb090AlphaDummy301 u) ≠
        (nb090AlphaDummy304 u) from (by
          unfold nb090AlphaDummy304;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0307 u) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy307 A), (nb090AlphaDummy310 u)), ((nb090AlphaDummy306 A),
        (nb090AlphaDummy309 u)), ((nb090AlphaDummy305 A), (nb090AlphaDummy308 u)),
        ((nb090AlphaDummy303 A), (nb090AlphaDummy304 u)), ((nb090AlphaDummy299 A),
        (nb090AlphaDummy301 u)), ((nb090AlphaDummy300 A), (nb090AlphaDummy302 u)),
        ((nb090AlphaDummy325 A), (nb090AlphaDummy326 u)), ((nb090AlphaDummy323 A),
        (nb090AlphaDummy324 u)), ((nb090AlphaDummy292 A), (nb090AlphaDummy294 u)),
        ((nb090AlphaDummy291 A), (nb090AlphaDummy293 u)), ((nb090AlphaDummy321 A),
        (nb090AlphaDummy322 u)), ((nb090AlphaDummy295 A), (nb090AlphaDummy296 u)),
        ((nb090AlphaDummy283 A), (nb090AlphaDummy284 u)), ((nb090AlphaDummy285 A),
        (nb090AlphaDummy286 u)), ((nb090AlphaDummy288 A), (nb090AlphaDummy290 u)),
        ((nb090AlphaDummy287 A), (nb090AlphaDummy289 u)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy306 A) ≠ (nb090AlphaDummy313 A) from (by
          unfold
            nb090AlphaDummy313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0312
                    A)
                  0)))) (show (nb090AlphaDummy309 u) ≠ (nb090AlphaDummy314 u) from (by
          unfold
            nb090AlphaDummy314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0313
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy306 A) ≠
        (nb090AlphaDummy311 A) from (by
          unfold
            nb090AlphaDummy311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0310
                    A)
                  0)))) (show (nb090AlphaDummy309 u) ≠ (nb090AlphaDummy312 u) from (by
          unfold
            nb090AlphaDummy312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0311
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy299
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy301 u))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy307 A) ≠ (nb090AlphaDummy313 A) from (by
          unfold
            nb090AlphaDummy313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0316
                    A)
                  0)))) (show (nb090AlphaDummy310 u) ≠ (nb090AlphaDummy314 u) from (by
          unfold
            nb090AlphaDummy314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0317
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy307 A) ≠
        (nb090AlphaDummy311 A) from (by
          unfold
            nb090AlphaDummy311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0314
                    A)
                  0)))) (show (nb090AlphaDummy310 u) ≠ (nb090AlphaDummy312 u) from (by
          unfold
            nb090AlphaDummy312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0315
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy306 A) ≠ (nb090AlphaDummy313 A) from (by
          unfold
            nb090AlphaDummy313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0312
                    A)
                  0)))) (show (nb090AlphaDummy309 u) ≠ (nb090AlphaDummy314 u) from (by
          unfold
            nb090AlphaDummy314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0313
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy306 A) ≠
        (nb090AlphaDummy311 A) from (by
          unfold
            nb090AlphaDummy311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0310
                    A)
                  0)))) (show (nb090AlphaDummy309 u) ≠ (nb090AlphaDummy312 u) from (by
          unfold
            nb090AlphaDummy312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0311
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy299
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy301 u))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy307 A) ≠ (nb090AlphaDummy313 A) from (by
          unfold
            nb090AlphaDummy313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0316
                    A)
                  0)))) (show (nb090AlphaDummy310 u) ≠ (nb090AlphaDummy314 u) from (by
          unfold
            nb090AlphaDummy314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0317
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy307 A) ≠
        (nb090AlphaDummy311 A) from (by
          unfold
            nb090AlphaDummy311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0314
                    A)
                  0)))) (show (nb090AlphaDummy310 u) ≠ (nb090AlphaDummy312 u) from (by
          unfold
            nb090AlphaDummy312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0315
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy307 A), (nb090AlphaDummy310 u)), ((nb090AlphaDummy306 A),
        (nb090AlphaDummy309 u)), ((nb090AlphaDummy305 A), (nb090AlphaDummy308 u)),
        ((nb090AlphaDummy303 A), (nb090AlphaDummy304 u)), ((nb090AlphaDummy299 A),
        (nb090AlphaDummy301 u)), ((nb090AlphaDummy300 A), (nb090AlphaDummy302 u)),
        ((nb090AlphaDummy325 A), (nb090AlphaDummy326 u)), ((nb090AlphaDummy323 A),
        (nb090AlphaDummy324 u)), ((nb090AlphaDummy292 A), (nb090AlphaDummy294 u)),
        ((nb090AlphaDummy291 A), (nb090AlphaDummy293 u)), ((nb090AlphaDummy321 A),
        (nb090AlphaDummy322 u)), ((nb090AlphaDummy295 A), (nb090AlphaDummy296 u)),
        ((nb090AlphaDummy283 A), (nb090AlphaDummy284 u)), ((nb090AlphaDummy285 A),
        (nb090AlphaDummy286 u)), ((nb090AlphaDummy288 A), (nb090AlphaDummy290 u)),
        ((nb090AlphaDummy287 A), (nb090AlphaDummy289 u)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy299 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy301 u))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy299 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy301 u))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy306
        A) ≠ (nb090AlphaDummy317 A) from (by
          unfold
            nb090AlphaDummy317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0320
                    A)
                  0)))) (show (nb090AlphaDummy309 u) ≠ (nb090AlphaDummy318 u) from (by
          unfold
            nb090AlphaDummy318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0321
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy306 A) ≠
        (nb090AlphaDummy315 A) from (by
          unfold
            nb090AlphaDummy315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0318
                    A)
                  0)))) (show (nb090AlphaDummy309 u) ≠ (nb090AlphaDummy316 u) from (by
          unfold
            nb090AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0319
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy299
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy301 u))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy306 A) ≠ (nb090AlphaDummy317 A) from (by
          unfold
            nb090AlphaDummy317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0320
                    A)
                  0)))) (show (nb090AlphaDummy309 u) ≠ (nb090AlphaDummy318 u) from (by
          unfold
            nb090AlphaDummy318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0321
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy306 A) ≠
        (nb090AlphaDummy315 A) from (by
          unfold
            nb090AlphaDummy315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0318
                    A)
                  0)))) (show (nb090AlphaDummy309 u) ≠ (nb090AlphaDummy316 u) from (by
          unfold
            nb090AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0319
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy299
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy301 u))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy307
        A) ≠ (nb090AlphaDummy319 A) from (by
          unfold
            nb090AlphaDummy319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0324
                    A)
                  0)))) (show (nb090AlphaDummy310 u) ≠ (nb090AlphaDummy320 u) from (by
          unfold
            nb090AlphaDummy320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0325
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy307 A) ≠
        (nb090AlphaDummy315 A) from (by
          unfold
            nb090AlphaDummy315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0322
                    A)
                  0)))) (show (nb090AlphaDummy310 u) ≠ (nb090AlphaDummy316 u) from (by
          unfold
            nb090AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0323
                    u)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy307
        A) ≠ (nb090AlphaDummy319 A) from (by
          unfold
            nb090AlphaDummy319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0324
                    A)
                  0)))) (show (nb090AlphaDummy310 u) ≠ (nb090AlphaDummy320 u) from (by
          unfold
            nb090AlphaDummy320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0325
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy307 A) ≠
        (nb090AlphaDummy315 A) from (by
          unfold
            nb090AlphaDummy315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0322
                    A)
                  0)))) (show (nb090AlphaDummy310 u) ≠ (nb090AlphaDummy316 u) from (by
          unfold
            nb090AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0323
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy299 A) ≠ (nb090AlphaDummy303 A) from
                                    (by
                                      unfold nb090AlphaDummy303;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0306 A)
                                              0)))) (show
                                    (nb090AlphaDummy301 u) ≠ (nb090AlphaDummy304 u) from
                                    (by
                                      unfold nb090AlphaDummy304;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0307 u)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed
                                [((nb090AlphaDummy303 A), (nb090AlphaDummy304 u)),
                                  ((nb090AlphaDummy299 A), (nb090AlphaDummy301 u)),
                                  ((nb090AlphaDummy300 A), (nb090AlphaDummy302 u)),
                                  ((nb090AlphaDummy325 A), (nb090AlphaDummy326 u)),
                                  ((nb090AlphaDummy323 A), (nb090AlphaDummy324 u)),
                                  ((nb090AlphaDummy292 A), (nb090AlphaDummy294 u)),
                                  ((nb090AlphaDummy291 A), (nb090AlphaDummy293 u)),
                                  ((nb090AlphaDummy321 A), (nb090AlphaDummy322 u)),
                                  ((nb090AlphaDummy295 A), (nb090AlphaDummy296 u)),
                                  ((nb090AlphaDummy283 A), (nb090AlphaDummy284 u)),
                                  ((nb090AlphaDummy285 A), (nb090AlphaDummy286 u)),
                                  ((nb090AlphaDummy288 A), (nb090AlphaDummy290 u)),
                                  ((nb090AlphaDummy287 A), (nb090AlphaDummy289 u)),
                                  ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
                                  ((nb090AlphaDummy000 A), h),
                                  ((nb090AlphaDummy002 A), v),
                                  ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                    (nb090AlphaDummy004 v u A h))]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb090AlphaDummy299 A) ≠ (nb090AlphaDummy303 A) from (by
                                    unfold nb090AlphaDummy303;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0306 A)
                                            0)))) (show
                                  (nb090AlphaDummy301 u) ≠ (nb090AlphaDummy304 u) from (by
                                    unfold nb090AlphaDummy304;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0307 u)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy299 A) ≠ (nb090AlphaDummy303 A) from
                                    (by
                                      unfold nb090AlphaDummy303;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0306 A)
                                              0)))) (show
                                    (nb090AlphaDummy301 u) ≠ (nb090AlphaDummy304 u) from
                                    (by
                                      unfold nb090AlphaDummy304;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0307 u)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed
                                [((nb090AlphaDummy303 A), (nb090AlphaDummy304 u)),
                                  ((nb090AlphaDummy299 A), (nb090AlphaDummy301 u)),
                                  ((nb090AlphaDummy300 A), (nb090AlphaDummy302 u)),
                                  ((nb090AlphaDummy325 A), (nb090AlphaDummy326 u)),
                                  ((nb090AlphaDummy323 A), (nb090AlphaDummy324 u)),
                                  ((nb090AlphaDummy292 A), (nb090AlphaDummy294 u)),
                                  ((nb090AlphaDummy291 A), (nb090AlphaDummy293 u)),
                                  ((nb090AlphaDummy321 A), (nb090AlphaDummy322 u)),
                                  ((nb090AlphaDummy295 A), (nb090AlphaDummy296 u)),
                                  ((nb090AlphaDummy283 A), (nb090AlphaDummy284 u)),
                                  ((nb090AlphaDummy285 A), (nb090AlphaDummy286 u)),
                                  ((nb090AlphaDummy288 A), (nb090AlphaDummy290 u)),
                                  ((nb090AlphaDummy287 A), (nb090AlphaDummy289 u)),
                                  ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
                                  ((nb090AlphaDummy000 A), h),
                                  ((nb090AlphaDummy002 A), v),
                                  ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                    (nb090AlphaDummy004 v u A h))]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))

theorem nb090_wpp_notmem_1596 (A : Class) : (nb090AlphaDummy041 A) ∉ ((synC2nd)).fv :=
  by simpa only [nb090AlphaDummy041, fv_syn_c2nd] using (nb090_compact_fv_empty_0462 A)

theorem nb090_wpp_notmem_1597 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy043 v u h) ∉ ((synC2nd)).fv := by
  simpa only [nb090AlphaDummy043, fv_syn_c2nd] using
    (nb090_compact_fv_empty_0463 v u h)

theorem nb090_compact_envfresh_0275 (v : Var) (u : Var) (A : Class) (h : Var) :
    TEnvFresh
      [((nb090AlphaDummy283 A), (nb090AlphaDummy284 u)),
        ((nb090AlphaDummy285 A), (nb090AlphaDummy286 u)),
        ((nb090AlphaDummy288 A), (nb090AlphaDummy290 u)),
        ((nb090AlphaDummy287 A), (nb090AlphaDummy289 u)),
        ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      ((synC2nd)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb090AlphaDummy283 A) (nb090AlphaDummy284 u)
      (nb090_wpp_notmem_0838 A) (nb090_wpp_notmem_0839 u)
      (TEnvFresh.consFresh (nb090AlphaDummy285 A) (nb090AlphaDummy286 u)
        (nb090_wpp_notmem_0840 A) (nb090_wpp_notmem_0841 u)
        (TEnvFresh.consFresh (nb090AlphaDummy288 A) (nb090AlphaDummy290 u)
          (nb090_wpp_notmem_0842 A) (nb090_wpp_notmem_0843 u)
          (TEnvFresh.consFresh (nb090AlphaDummy287 A) (nb090AlphaDummy289 u)
            (nb090_wpp_notmem_0844 A) (nb090_wpp_notmem_0845 u)
            (TEnvFresh.consFresh (nb090AlphaDummy041 A) (nb090AlphaDummy043 v u h)
              (nb090_wpp_notmem_1596 A) (nb090_wpp_notmem_1597 v u h)
              (TEnvFresh.consFresh (nb090AlphaDummy000 A) h (nb090_wpp_notmem_0846 A)
                (nb090_wpp_notmem_0847 h)
                (TEnvFresh.consFresh (nb090AlphaDummy002 A) v (nb090_wpp_notmem_0848 A)
                  (nb090_wpp_notmem_0849 v) (TEnvFresh.consFresh (nb090AlphaDummy001 A) u
                    (nb090_wpp_notmem_0850 A) (nb090_wpp_notmem_0851 u)
                    (TEnvFresh.consFresh (nb090AlphaDummy003 A)
                      (nb090AlphaDummy004 v u A h) (nb090_wpp_notmem_0852 A)
                      (nb090_wpp_notmem_0853 v u A h) (TEnvFresh.nil ((synC2nd)).fv))))))))))

/-- Checked nominal proof certificate identified upstream as `nb090_wpp_refl_0275`. -/
@[expose]
noncomputable def nb090WppRefl0275 (v : Var) (u : Var) (A : Class) (h : Var) :
    TReflOn
      [((nb090AlphaDummy283 A), (nb090AlphaDummy284 u)),
        ((nb090AlphaDummy285 A), (nb090AlphaDummy286 u)),
        ((nb090AlphaDummy288 A), (nb090AlphaDummy290 u)),
        ((nb090AlphaDummy287 A), (nb090AlphaDummy289 u)),
        ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      ((synC2nd)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0275 v u A h)

theorem nb090_compact_fv_empty_0464 (A : Class) :
    (nb090AlphaDummy042 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0465 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy044 v u h) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
