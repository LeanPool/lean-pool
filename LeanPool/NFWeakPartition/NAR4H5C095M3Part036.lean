/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4H5C095M3Part036Block001


/-! NF weak partition development: NAR4H5C095M3Part036. -/


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

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0081`. -/
@[expose]
noncomputable def nb095SplitAlpha0081 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy261 D R S_cls E), (nb095AlphaDummy262 x R)),
        ((nb095AlphaDummy259 D R S_cls E), (nb095AlphaDummy260 x R)),
        ((nb095AlphaDummy250 D R S_cls E), (nb095AlphaDummy252 x R)),
        ((nb095AlphaDummy249 D R S_cls E), (nb095AlphaDummy251 x R)),
        ((nb095AlphaDummy247 D R S_cls E), (nb095AlphaDummy248 x D R)),
        ((nb095AlphaDummy245 D R S_cls E), (nb095AlphaDummy246 x D R)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy261 D R S_cls E))
          (Class.cab (nb095AlphaDummy255 D R S_cls E)
            (synWrex (nb095AlphaDummy256 D R S_cls E)
              (Class.cv (nb095AlphaDummy250 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy255 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy256 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy261 D R S_cls E))
            (Class.cab (nb095AlphaDummy255 D R S_cls E)
              (synWrex (nb095AlphaDummy256 D R S_cls E)
                (Class.cv (nb095AlphaDummy250 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy255 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy256 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy262 x R))
          (Class.cab (nb095AlphaDummy257 x R)
            (synWrex (nb095AlphaDummy258 x R) (Class.cv (nb095AlphaDummy252 x R))
              (Wff.classEq (Class.cv (nb095AlphaDummy257 x R))
                (synCphi (Class.cv (nb095AlphaDummy258 x R))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy262 x R))
            (Class.cab (nb095AlphaDummy257 x R)
              (synWrex (nb095AlphaDummy258 x R) (Class.cv (nb095AlphaDummy252 x R))
                (Wff.classEq (Class.cv (nb095AlphaDummy257 x R))
                  (synCphi (Class.cv (nb095AlphaDummy258 x R))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095AlphaDummy250 D R S_cls E) ≠
                      (nb095AlphaDummy256 D R S_cls E) from (by
                      unfold nb095AlphaDummy256;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0258 D R S_cls E) 1))))
                  (show (nb095AlphaDummy252 x R) ≠ (nb095AlphaDummy258 x R) from (by
                      unfold nb095AlphaDummy258;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0260 x R) 1)))) (TAlphaVar.there
                    (show (nb095AlphaDummy250 D R S_cls E) ≠
                        (nb095AlphaDummy255 D R S_cls E) from (by
                        unfold nb095AlphaDummy255;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0258 D R S_cls E) 0))))
                    (show (nb095AlphaDummy252 x R) ≠ (nb095AlphaDummy257 x R) from (by
                        unfold nb095AlphaDummy257;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0260 x R) 0))))
                    (TAlphaVar.there (show (nb095AlphaDummy250 D R S_cls E) ≠
                          (nb095AlphaDummy261 D R S_cls E) from (by
                          unfold nb095AlphaDummy261;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0262 D R S_cls E)
                                  0))))
                      (show (nb095AlphaDummy252 x R) ≠ (nb095AlphaDummy262 x R) from (by
                          unfold nb095AlphaDummy262;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0263 x R) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy250 D R S_cls E) ≠
                            (nb095AlphaDummy259 D R S_cls E) from (by
                            unfold nb095AlphaDummy259;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0259 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy252 x R) ≠ (nb095AlphaDummy260 x R) from (by
                            unfold nb095AlphaDummy260;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0261 x R) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095AlphaDummy250 D R S_cls E))).fv ∪
                      ((Class.cv (nb095AlphaDummy249 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095AlphaDummy252 x R))).fv ∪
                      ((Class.cv (nb095AlphaDummy251 x R))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095AlphaDummy256 D R S_cls E) ≠
                              (nb095AlphaDummy263 D R S_cls E) from (by
                              unfold nb095AlphaDummy263;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0264 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy258 x R) ≠ (nb095AlphaDummy265 x R) from
                            (by
                              unfold nb095AlphaDummy265;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0265 x R) 0))))
                          (TAlphaVar.there (show (nb095AlphaDummy256 D R S_cls E) ≠
                                (nb095AlphaDummy264 D R S_cls E) from (by
                                unfold nb095AlphaDummy264;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0264 D R S_cls E) 1)))) (show
                              (nb095AlphaDummy258 x R) ≠ (nb095AlphaDummy266 x R) from (by
                                unfold nb095AlphaDummy266;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0265 x R) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095AlphaDummy256 D R S_cls E))).fv) (by decide))
                          (freshVar_injective
                            (((Class.cv (nb095AlphaDummy258 x R))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy263 D R S_cls E) ≠
        (nb095AlphaDummy270 D R S_cls E) from (by
          unfold nb095AlphaDummy270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0268 D R S_cls
                    E)
                  1)))) (show (nb095AlphaDummy265 x R) ≠ (nb095AlphaDummy273 x R) from (by
          unfold nb095AlphaDummy273;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0269 x R) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy263 D R S_cls E) ≠ (nb095AlphaDummy269 D R S_cls E) from (by
          unfold nb095AlphaDummy269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0268 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy265 x R) ≠ (nb095AlphaDummy272 x R) from (by
          unfold nb095AlphaDummy272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0269 x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy263 D R S_cls E) ≠
        (nb095AlphaDummy267 D R S_cls E) from (by
          unfold nb095AlphaDummy267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0266 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy265 x R) ≠ (nb095AlphaDummy268 x R) from (by
          unfold nb095AlphaDummy268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0267 x R)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy271 D R S_cls E), (nb095AlphaDummy274 x R)),
        ((nb095AlphaDummy270 D R S_cls E), (nb095AlphaDummy273 x R)),
        ((nb095AlphaDummy269 D R S_cls E), (nb095AlphaDummy272 x R)),
        ((nb095AlphaDummy267 D R S_cls E), (nb095AlphaDummy268 x R)),
        ((nb095AlphaDummy263 D R S_cls E), (nb095AlphaDummy265 x R)),
        ((nb095AlphaDummy264 D R S_cls E), (nb095AlphaDummy266 x R)),
        ((nb095AlphaDummy256 D R S_cls E), (nb095AlphaDummy258 x R)),
        ((nb095AlphaDummy255 D R S_cls E), (nb095AlphaDummy257 x R)),
        ((nb095AlphaDummy261 D R S_cls E), (nb095AlphaDummy262 x R)),
        ((nb095AlphaDummy259 D R S_cls E), (nb095AlphaDummy260 x R)),
        ((nb095AlphaDummy250 D R S_cls E), (nb095AlphaDummy252 x R)),
        ((nb095AlphaDummy249 D R S_cls E), (nb095AlphaDummy251 x R)),
        ((nb095AlphaDummy247 D R S_cls E), (nb095AlphaDummy248 x D R)),
        ((nb095AlphaDummy245 D R S_cls E), (nb095AlphaDummy246 x D R)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy270
        D R S_cls E) ≠ (nb095AlphaDummy277 D R S_cls E) from (by
          unfold
            nb095AlphaDummy277;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0272
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy273 x R) ≠ (nb095AlphaDummy278 x R) from (by
          unfold
            nb095AlphaDummy278;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0273
                    x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy270 D R S_cls E) ≠
        (nb095AlphaDummy275 D R S_cls E) from (by
          unfold
            nb095AlphaDummy275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0270
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy273 x R) ≠ (nb095AlphaDummy276 x R) from (by
          unfold
            nb095AlphaDummy276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0271
                    x R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy263
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy265 x R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy271 D R S_cls E) ≠ (nb095AlphaDummy277
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy277;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0276
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy274 x R) ≠ (nb095AlphaDummy278 x R) from (by
          unfold
            nb095AlphaDummy278;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0277
                    x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy271 D R S_cls E) ≠
        (nb095AlphaDummy275 D R S_cls E) from (by
          unfold
            nb095AlphaDummy275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0274
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy274 x R) ≠ (nb095AlphaDummy276 x R) from (by
          unfold
            nb095AlphaDummy276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0275
                    x R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy270 D R S_cls E) ≠ (nb095AlphaDummy277
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy277;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0272
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy273 x R) ≠ (nb095AlphaDummy278 x R) from (by
          unfold
            nb095AlphaDummy278;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0273
                    x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy270 D R S_cls E) ≠
        (nb095AlphaDummy275 D R S_cls E) from (by
          unfold
            nb095AlphaDummy275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0270
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy273 x R) ≠ (nb095AlphaDummy276 x R) from (by
          unfold
            nb095AlphaDummy276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0271
                    x R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy263
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy265 x R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy271 D R S_cls E) ≠ (nb095AlphaDummy277
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy277;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0276
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy274 x R) ≠ (nb095AlphaDummy278 x R) from (by
          unfold
            nb095AlphaDummy278;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0277
                    x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy271 D R S_cls E) ≠
        (nb095AlphaDummy275 D R S_cls E) from (by
          unfold
            nb095AlphaDummy275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0274
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy274 x R) ≠ (nb095AlphaDummy276 x R) from (by
          unfold
            nb095AlphaDummy276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0275
                    x R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy271 D R S_cls E), (nb095AlphaDummy274 x R)),
        ((nb095AlphaDummy270 D R S_cls E), (nb095AlphaDummy273 x R)),
        ((nb095AlphaDummy269 D R S_cls E), (nb095AlphaDummy272 x R)),
        ((nb095AlphaDummy267 D R S_cls E), (nb095AlphaDummy268 x R)),
        ((nb095AlphaDummy263 D R S_cls E), (nb095AlphaDummy265 x R)),
        ((nb095AlphaDummy264 D R S_cls E), (nb095AlphaDummy266 x R)),
        ((nb095AlphaDummy256 D R S_cls E), (nb095AlphaDummy258 x R)),
        ((nb095AlphaDummy255 D R S_cls E), (nb095AlphaDummy257 x R)),
        ((nb095AlphaDummy261 D R S_cls E), (nb095AlphaDummy262 x R)),
        ((nb095AlphaDummy259 D R S_cls E), (nb095AlphaDummy260 x R)),
        ((nb095AlphaDummy250 D R S_cls E), (nb095AlphaDummy252 x R)),
        ((nb095AlphaDummy249 D R S_cls E), (nb095AlphaDummy251 x R)),
        ((nb095AlphaDummy247 D R S_cls E), (nb095AlphaDummy248 x D R)),
        ((nb095AlphaDummy245 D R S_cls E), (nb095AlphaDummy246 x D R)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy263 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy265 x R))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy263 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy265 x R))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy270
        D R S_cls E) ≠ (nb095AlphaDummy281 D R S_cls E) from (by
          unfold
            nb095AlphaDummy281;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0280
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy273 x R) ≠ (nb095AlphaDummy282 x R) from (by
          unfold
            nb095AlphaDummy282;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0281
                    x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy270 D R S_cls E) ≠
        (nb095AlphaDummy279 D R S_cls E) from (by
          unfold
            nb095AlphaDummy279;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0278
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy273 x R) ≠ (nb095AlphaDummy280 x R) from (by
          unfold
            nb095AlphaDummy280;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0279
                    x R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy263
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy265 x R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy270 D R S_cls E) ≠ (nb095AlphaDummy281
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy281;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0280
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy273 x R) ≠ (nb095AlphaDummy282 x R) from (by
          unfold
            nb095AlphaDummy282;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0281
                    x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy270 D R S_cls E) ≠
        (nb095AlphaDummy279 D R S_cls E) from (by
          unfold
            nb095AlphaDummy279;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0278
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy273 x R) ≠ (nb095AlphaDummy280 x R) from (by
          unfold
            nb095AlphaDummy280;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0279
                    x R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy263
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy265 x R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy271
        D R S_cls E) ≠ (nb095AlphaDummy283 D R S_cls E) from (by
          unfold
            nb095AlphaDummy283;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0284
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy274 x R) ≠ (nb095AlphaDummy284 x R) from (by
          unfold
            nb095AlphaDummy284;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0285
                    x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy271 D R S_cls E) ≠
        (nb095AlphaDummy279 D R S_cls E) from (by
          unfold
            nb095AlphaDummy279;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0282
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy274 x R) ≠ (nb095AlphaDummy280 x R) from (by
          unfold
            nb095AlphaDummy280;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0283
                    x R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy271
        D R S_cls E) ≠ (nb095AlphaDummy283 D R S_cls E) from (by
          unfold
            nb095AlphaDummy283;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0284
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy274 x R) ≠ (nb095AlphaDummy284 x R) from (by
          unfold
            nb095AlphaDummy284;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0285
                    x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy271 D R S_cls E) ≠
        (nb095AlphaDummy279 D R S_cls E) from (by
          unfold
            nb095AlphaDummy279;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0282
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy274 x R) ≠ (nb095AlphaDummy280 x R) from (by
          unfold
            nb095AlphaDummy280;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0283
                    x R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy263 D R S_cls E) ≠
                                        (nb095AlphaDummy267 D R S_cls E) from (by
                                        unfold nb095AlphaDummy267;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0266 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy265 x R) ≠ (nb095AlphaDummy268 x R)
                                      from (by
                                        unfold nb095AlphaDummy268;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0267 x R) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy267 D R S_cls E),
                                      (nb095AlphaDummy268 x R)),
                                    ((nb095AlphaDummy263 D R S_cls E),
                                      (nb095AlphaDummy265 x R)),
                                    ((nb095AlphaDummy264 D R S_cls E),
                                      (nb095AlphaDummy266 x R)),
                                    ((nb095AlphaDummy256 D R S_cls E),
                                      (nb095AlphaDummy258 x R)),
                                    ((nb095AlphaDummy255 D R S_cls E),
                                      (nb095AlphaDummy257 x R)),
                                    ((nb095AlphaDummy261 D R S_cls E),
                                      (nb095AlphaDummy262 x R)),
                                    ((nb095AlphaDummy259 D R S_cls E),
                                      (nb095AlphaDummy260 x R)),
                                    ((nb095AlphaDummy250 D R S_cls E),
                                      (nb095AlphaDummy252 x R)),
                                    ((nb095AlphaDummy249 D R S_cls E),
                                      (nb095AlphaDummy251 x R)),
                                    ((nb095AlphaDummy247 D R S_cls E),
                                      (nb095AlphaDummy248 x D R)),
                                    ((nb095AlphaDummy245 D R S_cls E),
                                      (nb095AlphaDummy246 x D R)),
                                    ((nb095AlphaDummy004 D R S_cls E),
                                      (nb095AlphaDummy006 x u D R S_cls f E)),
                                    ((nb095AlphaDummy003 D R S_cls E),
                                      (nb095AlphaDummy005 x u D R S_cls f E)),
                                    ((nb095AlphaDummy001 D R S_cls E), u),
                                    ((nb095AlphaDummy002 D R S_cls E), x),
                                    ((nb095AlphaDummy000 D R S_cls E), f)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy263 D R S_cls E) ≠
                                      (nb095AlphaDummy267 D R S_cls E) from (by
                                      unfold nb095AlphaDummy267;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0266 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy265 x R) ≠ (nb095AlphaDummy268 x R)
                                    from (by
                                      unfold nb095AlphaDummy268;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0267 x R)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy263 D R S_cls E) ≠
                                        (nb095AlphaDummy267 D R S_cls E) from (by
                                        unfold nb095AlphaDummy267;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0266 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy265 x R) ≠ (nb095AlphaDummy268 x R)
                                      from (by
                                        unfold nb095AlphaDummy268;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0267 x R) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy267 D R S_cls E),
                                      (nb095AlphaDummy268 x R)),
                                    ((nb095AlphaDummy263 D R S_cls E),
                                      (nb095AlphaDummy265 x R)),
                                    ((nb095AlphaDummy264 D R S_cls E),
                                      (nb095AlphaDummy266 x R)),
                                    ((nb095AlphaDummy256 D R S_cls E),
                                      (nb095AlphaDummy258 x R)),
                                    ((nb095AlphaDummy255 D R S_cls E),
                                      (nb095AlphaDummy257 x R)),
                                    ((nb095AlphaDummy261 D R S_cls E),
                                      (nb095AlphaDummy262 x R)),
                                    ((nb095AlphaDummy259 D R S_cls E),
                                      (nb095AlphaDummy260 x R)),
                                    ((nb095AlphaDummy250 D R S_cls E),
                                      (nb095AlphaDummy252 x R)),
                                    ((nb095AlphaDummy249 D R S_cls E),
                                      (nb095AlphaDummy251 x R)),
                                    ((nb095AlphaDummy247 D R S_cls E),
                                      (nb095AlphaDummy248 x D R)),
                                    ((nb095AlphaDummy245 D R S_cls E),
                                      (nb095AlphaDummy246 x D R)),
                                    ((nb095AlphaDummy004 D R S_cls E),
                                      (nb095AlphaDummy006 x u D R S_cls f E)),
                                    ((nb095AlphaDummy003 D R S_cls E),
                                      (nb095AlphaDummy005 x u D R S_cls f E)),
                                    ((nb095AlphaDummy001 D R S_cls E), u),
                                    ((nb095AlphaDummy002 D R S_cls E), x),
                                    ((nb095AlphaDummy000 D R S_cls E), f)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb095AlphaDummy250 D R S_cls E) ≠
                        (nb095AlphaDummy256 D R S_cls E) from (by
                        unfold nb095AlphaDummy256;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0258 D R S_cls E) 1))))
                    (show (nb095AlphaDummy252 x R) ≠ (nb095AlphaDummy258 x R) from (by
                        unfold nb095AlphaDummy258;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0260 x R) 1))))
                    (TAlphaVar.there (show (nb095AlphaDummy250 D R S_cls E) ≠
                          (nb095AlphaDummy255 D R S_cls E) from (by
                          unfold nb095AlphaDummy255;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0258 D R S_cls E)
                                  0))))
                      (show (nb095AlphaDummy252 x R) ≠ (nb095AlphaDummy257 x R) from (by
                          unfold nb095AlphaDummy257;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0260 x R) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy250 D R S_cls E) ≠
                            (nb095AlphaDummy261 D R S_cls E) from (by
                            unfold nb095AlphaDummy261;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0262 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy252 x R) ≠ (nb095AlphaDummy262 x R) from (by
                            unfold nb095AlphaDummy262;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0263 x R) 0))))
                        (TAlphaVar.there (show (nb095AlphaDummy250 D R S_cls E) ≠
                              (nb095AlphaDummy259 D R S_cls E) from (by
                              unfold nb095AlphaDummy259;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0259 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy252 x R) ≠ (nb095AlphaDummy260 x R) from
                            (by
                              unfold nb095AlphaDummy260;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0261 x R) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095AlphaDummy250 D R S_cls E))).fv ∪
                        ((Class.cv (nb095AlphaDummy249 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095AlphaDummy252 x R))).fv ∪
                        ((Class.cv (nb095AlphaDummy251 x R))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy256 D R S_cls E) ≠
                                (nb095AlphaDummy263 D R S_cls E) from (by
                                unfold nb095AlphaDummy263;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0264 D R S_cls E) 0)))) (show
                              (nb095AlphaDummy258 x R) ≠ (nb095AlphaDummy265 x R) from (by
                                unfold nb095AlphaDummy265;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0265 x R) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy256 D R S_cls E) ≠
                                  (nb095AlphaDummy264 D R S_cls E) from (by
                                  unfold nb095AlphaDummy264;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0264 D R S_cls E) 1)))) (show
                                (nb095AlphaDummy258 x R) ≠ (nb095AlphaDummy266 x R) from
                                (by
                                  unfold nb095AlphaDummy266;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0265 x R)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095AlphaDummy256 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095AlphaDummy258 x R))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy263 D R S_cls E) ≠ (nb095AlphaDummy270 D R S_cls E) from (by
          unfold nb095AlphaDummy270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0268 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy265 x R) ≠ (nb095AlphaDummy273 x R) from (by
          unfold nb095AlphaDummy273;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0269 x R)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy263 D R S_cls E) ≠
        (nb095AlphaDummy269 D R S_cls E) from (by
          unfold nb095AlphaDummy269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0268 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy265 x R) ≠ (nb095AlphaDummy272 x R) from (by
          unfold nb095AlphaDummy272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0269 x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy263 D R S_cls E) ≠
        (nb095AlphaDummy267 D R S_cls E) from (by
          unfold nb095AlphaDummy267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0266 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy265 x R) ≠ (nb095AlphaDummy268 x R) from (by
          unfold nb095AlphaDummy268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0267 x R)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy271 D R S_cls E), (nb095AlphaDummy274 x R)),
        ((nb095AlphaDummy270 D R S_cls E), (nb095AlphaDummy273 x R)),
        ((nb095AlphaDummy269 D R S_cls E), (nb095AlphaDummy272 x R)),
        ((nb095AlphaDummy267 D R S_cls E), (nb095AlphaDummy268 x R)),
        ((nb095AlphaDummy263 D R S_cls E), (nb095AlphaDummy265 x R)),
        ((nb095AlphaDummy264 D R S_cls E), (nb095AlphaDummy266 x R)),
        ((nb095AlphaDummy256 D R S_cls E), (nb095AlphaDummy258 x R)),
        ((nb095AlphaDummy255 D R S_cls E), (nb095AlphaDummy257 x R)),
        ((nb095AlphaDummy261 D R S_cls E), (nb095AlphaDummy262 x R)),
        ((nb095AlphaDummy259 D R S_cls E), (nb095AlphaDummy260 x R)),
        ((nb095AlphaDummy250 D R S_cls E), (nb095AlphaDummy252 x R)),
        ((nb095AlphaDummy249 D R S_cls E), (nb095AlphaDummy251 x R)),
        ((nb095AlphaDummy247 D R S_cls E), (nb095AlphaDummy248 x D R)),
        ((nb095AlphaDummy245 D R S_cls E), (nb095AlphaDummy246 x D R)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy270
        D R S_cls E) ≠ (nb095AlphaDummy277 D R S_cls E) from (by
          unfold
            nb095AlphaDummy277;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0272
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy273 x R) ≠ (nb095AlphaDummy278 x R) from (by
          unfold
            nb095AlphaDummy278;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0273
                    x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy270 D R S_cls E) ≠
        (nb095AlphaDummy275 D R S_cls E) from (by
          unfold
            nb095AlphaDummy275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0270
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy273 x R) ≠ (nb095AlphaDummy276 x R) from (by
          unfold
            nb095AlphaDummy276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0271
                    x R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy263
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy265 x R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy271 D R S_cls E) ≠ (nb095AlphaDummy277
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy277;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0276
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy274 x R) ≠ (nb095AlphaDummy278 x R) from (by
          unfold
            nb095AlphaDummy278;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0277
                    x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy271 D R S_cls E) ≠
        (nb095AlphaDummy275 D R S_cls E) from (by
          unfold
            nb095AlphaDummy275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0274
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy274 x R) ≠ (nb095AlphaDummy276 x R) from (by
          unfold
            nb095AlphaDummy276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0275
                    x R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy270 D R S_cls E) ≠ (nb095AlphaDummy277
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy277;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0272
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy273 x R) ≠ (nb095AlphaDummy278 x R) from (by
          unfold
            nb095AlphaDummy278;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0273
                    x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy270 D R S_cls E) ≠
        (nb095AlphaDummy275 D R S_cls E) from (by
          unfold
            nb095AlphaDummy275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0270
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy273 x R) ≠ (nb095AlphaDummy276 x R) from (by
          unfold
            nb095AlphaDummy276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0271
                    x R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy263
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy265 x R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy271 D R S_cls E) ≠ (nb095AlphaDummy277
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy277;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0276
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy274 x R) ≠ (nb095AlphaDummy278 x R) from (by
          unfold
            nb095AlphaDummy278;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0277
                    x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy271 D R S_cls E) ≠
        (nb095AlphaDummy275 D R S_cls E) from (by
          unfold
            nb095AlphaDummy275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0274
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy274 x R) ≠ (nb095AlphaDummy276 x R) from (by
          unfold
            nb095AlphaDummy276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0275
                    x R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy271 D R S_cls E), (nb095AlphaDummy274 x R)),
        ((nb095AlphaDummy270 D R S_cls E), (nb095AlphaDummy273 x R)),
        ((nb095AlphaDummy269 D R S_cls E), (nb095AlphaDummy272 x R)),
        ((nb095AlphaDummy267 D R S_cls E), (nb095AlphaDummy268 x R)),
        ((nb095AlphaDummy263 D R S_cls E), (nb095AlphaDummy265 x R)),
        ((nb095AlphaDummy264 D R S_cls E), (nb095AlphaDummy266 x R)),
        ((nb095AlphaDummy256 D R S_cls E), (nb095AlphaDummy258 x R)),
        ((nb095AlphaDummy255 D R S_cls E), (nb095AlphaDummy257 x R)),
        ((nb095AlphaDummy261 D R S_cls E), (nb095AlphaDummy262 x R)),
        ((nb095AlphaDummy259 D R S_cls E), (nb095AlphaDummy260 x R)),
        ((nb095AlphaDummy250 D R S_cls E), (nb095AlphaDummy252 x R)),
        ((nb095AlphaDummy249 D R S_cls E), (nb095AlphaDummy251 x R)),
        ((nb095AlphaDummy247 D R S_cls E), (nb095AlphaDummy248 x D R)),
        ((nb095AlphaDummy245 D R S_cls E), (nb095AlphaDummy246 x D R)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy263 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy265 x R))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy263 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy265 x R))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy270
        D R S_cls E) ≠ (nb095AlphaDummy281 D R S_cls E) from (by
          unfold
            nb095AlphaDummy281;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0280
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy273 x R) ≠ (nb095AlphaDummy282 x R) from (by
          unfold
            nb095AlphaDummy282;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0281
                    x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy270 D R S_cls E) ≠
        (nb095AlphaDummy279 D R S_cls E) from (by
          unfold
            nb095AlphaDummy279;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0278
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy273 x R) ≠ (nb095AlphaDummy280 x R) from (by
          unfold
            nb095AlphaDummy280;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0279
                    x R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy263
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy265 x R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy270 D R S_cls E) ≠ (nb095AlphaDummy281
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy281;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0280
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy273 x R) ≠ (nb095AlphaDummy282 x R) from (by
          unfold
            nb095AlphaDummy282;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0281
                    x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy270 D R S_cls E) ≠
        (nb095AlphaDummy279 D R S_cls E) from (by
          unfold
            nb095AlphaDummy279;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0278
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy273 x R) ≠ (nb095AlphaDummy280 x R) from (by
          unfold
            nb095AlphaDummy280;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0279
                    x R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy263
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy265 x R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy271
        D R S_cls E) ≠ (nb095AlphaDummy283 D R S_cls E) from (by
          unfold
            nb095AlphaDummy283;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0284
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy274 x R) ≠ (nb095AlphaDummy284 x R) from (by
          unfold
            nb095AlphaDummy284;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0285
                    x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy271 D R S_cls E) ≠
        (nb095AlphaDummy279 D R S_cls E) from (by
          unfold
            nb095AlphaDummy279;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0282
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy274 x R) ≠ (nb095AlphaDummy280 x R) from (by
          unfold
            nb095AlphaDummy280;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0283
                    x R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy271
        D R S_cls E) ≠ (nb095AlphaDummy283 D R S_cls E) from (by
          unfold
            nb095AlphaDummy283;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0284
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy274 x R) ≠ (nb095AlphaDummy284 x R) from (by
          unfold
            nb095AlphaDummy284;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0285
                    x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy271 D R S_cls E) ≠
        (nb095AlphaDummy279 D R S_cls E) from (by
          unfold
            nb095AlphaDummy279;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0282
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy274 x R) ≠ (nb095AlphaDummy280 x R) from (by
          unfold
            nb095AlphaDummy280;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0283
                    x R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy263 D R S_cls E) ≠
        (nb095AlphaDummy267 D R S_cls E) from (by
                                          unfold nb095AlphaDummy267;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0266 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy265 x R) ≠
        (nb095AlphaDummy268 x R) from (by
                                          unfold nb095AlphaDummy268;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0267 x R) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy267 D R S_cls E),
                                        (nb095AlphaDummy268 x R)),
                                      ((nb095AlphaDummy263 D R S_cls E),
                                        (nb095AlphaDummy265 x R)),
                                      ((nb095AlphaDummy264 D R S_cls E),
                                        (nb095AlphaDummy266 x R)),
                                      ((nb095AlphaDummy256 D R S_cls E),
                                        (nb095AlphaDummy258 x R)),
                                      ((nb095AlphaDummy255 D R S_cls E),
                                        (nb095AlphaDummy257 x R)),
                                      ((nb095AlphaDummy261 D R S_cls E),
                                        (nb095AlphaDummy262 x R)),
                                      ((nb095AlphaDummy259 D R S_cls E),
                                        (nb095AlphaDummy260 x R)),
                                      ((nb095AlphaDummy250 D R S_cls E),
                                        (nb095AlphaDummy252 x R)),
                                      ((nb095AlphaDummy249 D R S_cls E),
                                        (nb095AlphaDummy251 x R)),
                                      ((nb095AlphaDummy247 D R S_cls E),
                                        (nb095AlphaDummy248 x D R)),
                                      ((nb095AlphaDummy245 D R S_cls E),
                                        (nb095AlphaDummy246 x D R)),
                                      ((nb095AlphaDummy004 D R S_cls E),
                                        (nb095AlphaDummy006 x u D R S_cls f E)),
                                      ((nb095AlphaDummy003 D R S_cls E),
                                        (nb095AlphaDummy005 x u D R S_cls f E)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy263 D R S_cls E) ≠
                                        (nb095AlphaDummy267 D R S_cls E) from (by
                                        unfold nb095AlphaDummy267;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0266 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy265 x R) ≠ (nb095AlphaDummy268 x R)
                                      from (by
                                        unfold nb095AlphaDummy268;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0267 x R) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy263 D R S_cls E) ≠
        (nb095AlphaDummy267 D R S_cls E) from (by
                                          unfold nb095AlphaDummy267;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0266 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy265 x R) ≠
        (nb095AlphaDummy268 x R) from (by
                                          unfold nb095AlphaDummy268;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0267 x R) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy267 D R S_cls E),
                                        (nb095AlphaDummy268 x R)),
                                      ((nb095AlphaDummy263 D R S_cls E),
                                        (nb095AlphaDummy265 x R)),
                                      ((nb095AlphaDummy264 D R S_cls E),
                                        (nb095AlphaDummy266 x R)),
                                      ((nb095AlphaDummy256 D R S_cls E),
                                        (nb095AlphaDummy258 x R)),
                                      ((nb095AlphaDummy255 D R S_cls E),
                                        (nb095AlphaDummy257 x R)),
                                      ((nb095AlphaDummy261 D R S_cls E),
                                        (nb095AlphaDummy262 x R)),
                                      ((nb095AlphaDummy259 D R S_cls E),
                                        (nb095AlphaDummy260 x R)),
                                      ((nb095AlphaDummy250 D R S_cls E),
                                        (nb095AlphaDummy252 x R)),
                                      ((nb095AlphaDummy249 D R S_cls E),
                                        (nb095AlphaDummy251 x R)),
                                      ((nb095AlphaDummy247 D R S_cls E),
                                        (nb095AlphaDummy248 x D R)),
                                      ((nb095AlphaDummy245 D R S_cls E),
                                        (nb095AlphaDummy246 x D R)),
                                      ((nb095AlphaDummy004 D R S_cls E),
                                        (nb095AlphaDummy006 x u D R S_cls f E)),
                                      ((nb095AlphaDummy003 D R S_cls E),
                                        (nb095AlphaDummy005 x u D R S_cls f E)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
