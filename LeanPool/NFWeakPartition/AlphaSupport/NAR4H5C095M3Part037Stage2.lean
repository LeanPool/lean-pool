/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4H5C095M3Part037Stage1


/-! NF weak partition development: NAR4H5C095M3Part037. -/


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
noncomputable def nb095_wpp_refl_0275 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_R_f : f ∉ R.fv) (dv_R_u : u ∉ R.fv)
    (dv_R_x : x ∉ R.fv) :
    TReflOn
      [((nb095_alpha_dummy_250 D R S_cls E), (nb095_alpha_dummy_252 x R)),
        ((nb095_alpha_dummy_249 D R S_cls E), (nb095_alpha_dummy_251 x R)),
        ((nb095_alpha_dummy_247 D R S_cls E), (nb095_alpha_dummy_248 x D R)),
        ((nb095_alpha_dummy_245 D R S_cls E), (nb095_alpha_dummy_246 x D R)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      ((syn_ccnv (syn_cdif R (syn_cid)))).fv :=
  TEnvFresh.reflOn (nb095_compact_envfresh_0282 x u D R S_cls f E dv_R_f dv_R_u dv_R_x)

@[expose]
noncomputable def nb095_split_alpha_0083 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_585 D R S_cls E), (nb095_alpha_dummy_586 x u D R S_cls f E)),
        ((nb095_alpha_dummy_583 D R S_cls E), (nb095_alpha_dummy_584 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_585 D R S_cls E))
          (Class.cab (nb095_alpha_dummy_579 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_580 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_579 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_580 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_585 D R S_cls E))
            (Class.cab (nb095_alpha_dummy_579 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_580 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_579 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_580 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_586 x u D R S_cls f E))
          (Class.cab (nb095_alpha_dummy_581 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_582 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_581 x u D R S_cls f E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_586 x u D R S_cls f E))
            (Class.cab (nb095_alpha_dummy_581 x u D R S_cls f E)
              (syn_wrex (nb095_alpha_dummy_582 x u D R S_cls f E)
                (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_581 x u D R S_cls f E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095_alpha_dummy_003 D R S_cls E) ≠
                      (nb095_alpha_dummy_580 D R S_cls E) from (by
                      unfold nb095_alpha_dummy_580;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0602 D R S_cls E) 1)))) (show
                    (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
                      (nb095_alpha_dummy_582 x u D R S_cls f E) from (by
                      unfold nb095_alpha_dummy_582;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0604 x u D R S_cls f E)
                              1)))) (TAlphaVar.there (show (nb095_alpha_dummy_003 D R S_cls E) ≠
                        (nb095_alpha_dummy_579 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_579;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0602 D R S_cls E) 0)))) (show
                      (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
                        (nb095_alpha_dummy_581 x u D R S_cls f E) from (by
                        unfold nb095_alpha_dummy_581;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0604 x u D R S_cls f E)
                                0)))) (TAlphaVar.there (show
                        (nb095_alpha_dummy_003 D R S_cls E) ≠
                          (nb095_alpha_dummy_585 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_585;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0606 D R S_cls E)
                                  0)))) (show (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
                          (nb095_alpha_dummy_586 x u D R S_cls f E) from (by
                          unfold nb095_alpha_dummy_586;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar
                                  (nb095_support_mem_0607 x u D R S_cls f E) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_003 D R S_cls E) ≠
                            (nb095_alpha_dummy_583 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_583;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0603 D R S_cls E)
                                    0)))) (show (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
                            (nb095_alpha_dummy_584 x u D R S_cls f E) from (by
                            unfold nb095_alpha_dummy_584;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar
                                    (nb095_support_mem_0605 x u D R S_cls f E) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪ ((syn_cin R
                                        (syn_cxp (syn_cin D
        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv
        (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin D
        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv
        (nb095_alpha_dummy_002 D R S_cls E)))))))).fv ∪ ((syn_cin S_cls (syn_cxp (syn_cin E
        (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv
        (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
        (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv
        (nb095_alpha_dummy_001 D R S_cls E)))))))).fv ∪ ((syn_cin D
                                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                                        (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv ∪
                              ((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                                    (syn_csn (Class.cv
                                        (nb095_alpha_dummy_001 D R S_cls E)))))).fv)
                            (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((syn_cin R
                                        (syn_cxp (syn_cin D
        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))) (syn_cin D
        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))))).fv ∪
                                  ((syn_cin S_cls (syn_cxp (syn_cin E
        (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))) (syn_cin E
        (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))))).fv ∪
                                ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                                      (syn_csn (Class.cv x))))).fv ∪ ((syn_cin E
                                  (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                                    (syn_csn (Class.cv u))))).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095_alpha_dummy_003 D R S_cls E))).fv ∪
                      ((Class.cv (nb095_alpha_dummy_004 D R S_cls E))).fv) (by decide))
                  (freshVar_injective
                    (((Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))).fv ∪
                      ((Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095_alpha_dummy_580 D R S_cls E) ≠
                              (nb095_alpha_dummy_587 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_587;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0608 D R S_cls E)
                                      0)))) (show (nb095_alpha_dummy_582 x u D R S_cls f E) ≠
                              (nb095_alpha_dummy_589 x u D R S_cls f E) from (by
                              unfold nb095_alpha_dummy_589;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb095_support_mem_0609 x u D R S_cls f E) 0))))
                          (TAlphaVar.there (show (nb095_alpha_dummy_580 D R S_cls E) ≠
                                (nb095_alpha_dummy_588 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_588;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0608 D R S_cls E) 1)))) (show
                              (nb095_alpha_dummy_582 x u D R S_cls f E) ≠
                                (nb095_alpha_dummy_590 x u D R S_cls f E) from (by
                                unfold nb095_alpha_dummy_590;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0609 x u D R S_cls f E) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095_alpha_dummy_580 D R S_cls E))).fv) (by decide))
                          (freshVar_injective
                            (((Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_587 D R S_cls E) ≠
        (nb095_alpha_dummy_594 D R S_cls E) from (by
          unfold nb095_alpha_dummy_594;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0612 D R S_cls
                    E)
                  1)))) (show (nb095_alpha_dummy_589 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_597 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_597;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0613 x u D R
                    S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_587 D R S_cls E) ≠
        (nb095_alpha_dummy_593 D R S_cls E) from (by
          unfold nb095_alpha_dummy_593;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0612 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_589 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_596 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_596;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0613 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_587 D R S_cls E) ≠
        (nb095_alpha_dummy_591 D R S_cls E) from (by
          unfold nb095_alpha_dummy_591;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0610 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_589 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_592 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_592;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0611 x u D
                    R S_cls f E)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_595 D R S_cls E), (nb095_alpha_dummy_598 x u D R S_cls f E)),
        ((nb095_alpha_dummy_594 D R S_cls E), (nb095_alpha_dummy_597 x u D R S_cls f E)),
        ((nb095_alpha_dummy_593 D R S_cls E), (nb095_alpha_dummy_596 x u D R S_cls f E)),
        ((nb095_alpha_dummy_591 D R S_cls E), (nb095_alpha_dummy_592 x u D R S_cls f E)),
        ((nb095_alpha_dummy_587 D R S_cls E), (nb095_alpha_dummy_589 x u D R S_cls f E)),
        ((nb095_alpha_dummy_588 D R S_cls E), (nb095_alpha_dummy_590 x u D R S_cls f E)),
        ((nb095_alpha_dummy_580 D R S_cls E), (nb095_alpha_dummy_582 x u D R S_cls f E)),
        ((nb095_alpha_dummy_579 D R S_cls E), (nb095_alpha_dummy_581 x u D R S_cls f E)),
        ((nb095_alpha_dummy_585 D R S_cls E), (nb095_alpha_dummy_586 x u D R S_cls f E)),
        ((nb095_alpha_dummy_583 D R S_cls E), (nb095_alpha_dummy_584 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_594
        D R S_cls E) ≠ (nb095_alpha_dummy_601 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0616
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_597 x u D R S_cls f E) ≠ (nb095_alpha_dummy_602
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0617
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_594 D R S_cls E) ≠
        (nb095_alpha_dummy_599 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0614
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_597 x u D R S_cls f E) ≠ (nb095_alpha_dummy_600
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0615
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_587
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_589 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_595 D R S_cls E) ≠
        (nb095_alpha_dummy_601 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0620
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_598 x u D R S_cls f E) ≠ (nb095_alpha_dummy_602
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0621
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_595 D R S_cls E) ≠
        (nb095_alpha_dummy_599 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0618
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_598 x u D R S_cls f E) ≠ (nb095_alpha_dummy_600
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0619
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_594 D R S_cls E) ≠ (nb095_alpha_dummy_601
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0616
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_597 x u D R S_cls f E) ≠ (nb095_alpha_dummy_602
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0617
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_594 D R S_cls E) ≠
        (nb095_alpha_dummy_599 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0614
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_597 x u D R S_cls f E) ≠ (nb095_alpha_dummy_600
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0615
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_587
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_589 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_595 D R S_cls E) ≠
        (nb095_alpha_dummy_601 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0620
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_598 x u D R S_cls f E) ≠ (nb095_alpha_dummy_602
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0621
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_595 D R S_cls E) ≠
        (nb095_alpha_dummy_599 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0618
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_598 x u D R S_cls f E) ≠ (nb095_alpha_dummy_600
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0619
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_595 D R S_cls E), (nb095_alpha_dummy_598 x u D R S_cls f E)),
        ((nb095_alpha_dummy_594 D R S_cls E), (nb095_alpha_dummy_597 x u D R S_cls f E)),
        ((nb095_alpha_dummy_593 D R S_cls E), (nb095_alpha_dummy_596 x u D R S_cls f E)),
        ((nb095_alpha_dummy_591 D R S_cls E), (nb095_alpha_dummy_592 x u D R S_cls f E)),
        ((nb095_alpha_dummy_587 D R S_cls E), (nb095_alpha_dummy_589 x u D R S_cls f E)),
        ((nb095_alpha_dummy_588 D R S_cls E), (nb095_alpha_dummy_590 x u D R S_cls f E)),
        ((nb095_alpha_dummy_580 D R S_cls E), (nb095_alpha_dummy_582 x u D R S_cls f E)),
        ((nb095_alpha_dummy_579 D R S_cls E), (nb095_alpha_dummy_581 x u D R S_cls f E)),
        ((nb095_alpha_dummy_585 D R S_cls E), (nb095_alpha_dummy_586 x u D R S_cls f E)),
        ((nb095_alpha_dummy_583 D R S_cls E), (nb095_alpha_dummy_584 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_587 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_589 x u D R S_cls f E))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_587 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_589 x u D R S_cls f E))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_594
        D R S_cls E) ≠ (nb095_alpha_dummy_605 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0624
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_597 x u D R S_cls f E) ≠ (nb095_alpha_dummy_606
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0625
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_594 D R S_cls E) ≠
        (nb095_alpha_dummy_603 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0622
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_597 x u D R S_cls f E) ≠ (nb095_alpha_dummy_604
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0623
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_587
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_589 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_594 D R S_cls E) ≠
        (nb095_alpha_dummy_605 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0624
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_597 x u D R S_cls f E) ≠ (nb095_alpha_dummy_606
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0625
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_594 D R S_cls E) ≠
        (nb095_alpha_dummy_603 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0622
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_597 x u D R S_cls f E) ≠ (nb095_alpha_dummy_604
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0623
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_587
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_589 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_595 D R S_cls E) ≠ (nb095_alpha_dummy_607
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_607;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0628
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_598 x u D R S_cls f E) ≠ (nb095_alpha_dummy_608
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_608;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0629
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_595 D R S_cls E) ≠
        (nb095_alpha_dummy_603 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0626
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_598 x u D R S_cls f E) ≠ (nb095_alpha_dummy_604
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0627
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_595
        D R S_cls E) ≠ (nb095_alpha_dummy_607 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_607;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0628
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_598 x u D R S_cls f E) ≠ (nb095_alpha_dummy_608
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_608;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0629
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_595 D R S_cls E) ≠
        (nb095_alpha_dummy_603 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0626
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_598 x u D R S_cls f E) ≠ (nb095_alpha_dummy_604
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0627
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_587 D R S_cls E) ≠
                                        (nb095_alpha_dummy_591 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_591;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0610 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_589 x u D R S_cls f E) ≠
                                        (nb095_alpha_dummy_592 x u D R S_cls f E) from (by
                                        unfold nb095_alpha_dummy_592;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0611 x u D R S_cls f E)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb095_alpha_dummy_591 D R S_cls E),
                                      (nb095_alpha_dummy_592 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_587 D R S_cls E),
                                      (nb095_alpha_dummy_589 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_588 D R S_cls E),
                                      (nb095_alpha_dummy_590 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_580 D R S_cls E),
                                      (nb095_alpha_dummy_582 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_579 D R S_cls E),
                                      (nb095_alpha_dummy_581 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_585 D R S_cls E),
                                      (nb095_alpha_dummy_586 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_583 D R S_cls E),
                                      (nb095_alpha_dummy_584 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_004 D R S_cls E),
                                      (nb095_alpha_dummy_006 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_003 D R S_cls E),
                                      (nb095_alpha_dummy_005 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_001 D R S_cls E), u),
                                    ((nb095_alpha_dummy_002 D R S_cls E), x),
                                    ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095_alpha_dummy_587 D R S_cls E) ≠
                                      (nb095_alpha_dummy_591 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_591;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0610 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_589 x u D R S_cls f E) ≠
                                      (nb095_alpha_dummy_592 x u D R S_cls f E) from (by
                                      unfold nb095_alpha_dummy_592;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0611 x u D R S_cls f E)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_587 D R S_cls E) ≠
                                        (nb095_alpha_dummy_591 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_591;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0610 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_589 x u D R S_cls f E) ≠
                                        (nb095_alpha_dummy_592 x u D R S_cls f E) from (by
                                        unfold nb095_alpha_dummy_592;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0611 x u D R S_cls f E)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb095_alpha_dummy_591 D R S_cls E),
                                      (nb095_alpha_dummy_592 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_587 D R S_cls E),
                                      (nb095_alpha_dummy_589 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_588 D R S_cls E),
                                      (nb095_alpha_dummy_590 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_580 D R S_cls E),
                                      (nb095_alpha_dummy_582 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_579 D R S_cls E),
                                      (nb095_alpha_dummy_581 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_585 D R S_cls E),
                                      (nb095_alpha_dummy_586 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_583 D R S_cls E),
                                      (nb095_alpha_dummy_584 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_004 D R S_cls E),
                                      (nb095_alpha_dummy_006 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_003 D R S_cls E),
                                      (nb095_alpha_dummy_005 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_001 D R S_cls E), u),
                                    ((nb095_alpha_dummy_002 D R S_cls E), x),
                                    ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb095_alpha_dummy_003 D R S_cls E) ≠
                        (nb095_alpha_dummy_580 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_580;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0602 D R S_cls E) 1)))) (show
                      (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
                        (nb095_alpha_dummy_582 x u D R S_cls f E) from (by
                        unfold nb095_alpha_dummy_582;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0604 x u D R S_cls f E)
                                1)))) (TAlphaVar.there (show
                        (nb095_alpha_dummy_003 D R S_cls E) ≠
                          (nb095_alpha_dummy_579 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_579;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0602 D R S_cls E)
                                  0)))) (show (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
                          (nb095_alpha_dummy_581 x u D R S_cls f E) from (by
                          unfold nb095_alpha_dummy_581;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar
                                  (nb095_support_mem_0604 x u D R S_cls f E) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_003 D R S_cls E) ≠
                            (nb095_alpha_dummy_585 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_585;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0606 D R S_cls E)
                                    0)))) (show (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
                            (nb095_alpha_dummy_586 x u D R S_cls f E) from (by
                            unfold nb095_alpha_dummy_586;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar
                                    (nb095_support_mem_0607 x u D R S_cls f E) 0))))
                        (TAlphaVar.there (show (nb095_alpha_dummy_003 D R S_cls E) ≠
                              (nb095_alpha_dummy_583 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_583;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0603 D R S_cls E)
                                      0)))) (show (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
                              (nb095_alpha_dummy_584 x u D R S_cls f E) from (by
                              unfold nb095_alpha_dummy_584;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb095_support_mem_0605 x u D R S_cls f E) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪ ((syn_cin R
        (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv
        (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin D
        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv
        (nb095_alpha_dummy_002 D R S_cls E)))))))).fv ∪ ((syn_cin S_cls (syn_cxp (syn_cin E
        (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv
        (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E (syn_cima
        (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv
        (nb095_alpha_dummy_001 D R S_cls E)))))))).fv ∪ ((syn_cin D
                                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
        (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv ∪ ((syn_cin E
                                    (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn
                                        (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv)
                              (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((syn_cin R
        (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))))).fv ∪
                                    ((syn_cin S_cls (syn_cxp (syn_cin E (syn_cima
        (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))) (syn_cin E (syn_cima
        (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))))).fv ∪ ((syn_cin D
                                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                                        (syn_csn (Class.cv x))))).fv ∪ ((syn_cin E
                                    (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                                      (syn_csn (Class.cv u))))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095_alpha_dummy_003 D R S_cls E))).fv ∪
                        ((Class.cv (nb095_alpha_dummy_004 D R S_cls E))).fv) (by decide))
                    (freshVar_injective
                      (((Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))).fv ∪
                        ((Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_580 D R S_cls E) ≠
                                (nb095_alpha_dummy_587 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_587;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0608 D R S_cls E) 0)))) (show
                              (nb095_alpha_dummy_582 x u D R S_cls f E) ≠
                                (nb095_alpha_dummy_589 x u D R S_cls f E) from (by
                                unfold nb095_alpha_dummy_589;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0609 x u D R S_cls f E) 0))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_580 D R S_cls E) ≠
                                  (nb095_alpha_dummy_588 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_588;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0608 D R S_cls E) 1)))) (show
                                (nb095_alpha_dummy_582 x u D R S_cls f E) ≠
                                  (nb095_alpha_dummy_590 x u D R S_cls f E) from (by
                                  unfold nb095_alpha_dummy_590;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0609 x u D R S_cls f E) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_580 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E))).fv)
                              (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                          (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_587 D R S_cls E) ≠ (nb095_alpha_dummy_594 D R S_cls E) from (by
          unfold nb095_alpha_dummy_594;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0612 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_589 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_597 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_597;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0613 x u D R
                    S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_587 D R S_cls E) ≠
        (nb095_alpha_dummy_593 D R S_cls E) from (by
          unfold nb095_alpha_dummy_593;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0612 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_589 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_596 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_596;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0613 x u D
                    R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_587 D R S_cls E) ≠
        (nb095_alpha_dummy_591 D R S_cls E) from (by
          unfold nb095_alpha_dummy_591;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0610 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_589 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_592 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_592;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0611 x u
                    D R S_cls f E)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_595 D R S_cls E), (nb095_alpha_dummy_598 x u D R S_cls f E)),
        ((nb095_alpha_dummy_594 D R S_cls E), (nb095_alpha_dummy_597 x u D R S_cls f E)),
        ((nb095_alpha_dummy_593 D R S_cls E), (nb095_alpha_dummy_596 x u D R S_cls f E)),
        ((nb095_alpha_dummy_591 D R S_cls E), (nb095_alpha_dummy_592 x u D R S_cls f E)),
        ((nb095_alpha_dummy_587 D R S_cls E), (nb095_alpha_dummy_589 x u D R S_cls f E)),
        ((nb095_alpha_dummy_588 D R S_cls E), (nb095_alpha_dummy_590 x u D R S_cls f E)),
        ((nb095_alpha_dummy_580 D R S_cls E), (nb095_alpha_dummy_582 x u D R S_cls f E)),
        ((nb095_alpha_dummy_579 D R S_cls E), (nb095_alpha_dummy_581 x u D R S_cls f E)),
        ((nb095_alpha_dummy_585 D R S_cls E), (nb095_alpha_dummy_586 x u D R S_cls f E)),
        ((nb095_alpha_dummy_583 D R S_cls E), (nb095_alpha_dummy_584 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_594
        D R S_cls E) ≠ (nb095_alpha_dummy_601 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0616
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_597 x u D R S_cls f E) ≠ (nb095_alpha_dummy_602
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0617
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_594 D R S_cls E) ≠
        (nb095_alpha_dummy_599 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0614
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_597 x u D R S_cls f E) ≠ (nb095_alpha_dummy_600
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0615
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_587
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_589 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_595 D R S_cls E) ≠
        (nb095_alpha_dummy_601 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0620
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_598 x u D R S_cls f E) ≠ (nb095_alpha_dummy_602
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0621
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_595 D R S_cls E) ≠
        (nb095_alpha_dummy_599 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0618
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_598 x u D R S_cls f E) ≠ (nb095_alpha_dummy_600
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0619
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_594 D R S_cls E) ≠ (nb095_alpha_dummy_601
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0616
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_597 x u D R S_cls f E) ≠ (nb095_alpha_dummy_602
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0617
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_594 D R S_cls E) ≠
        (nb095_alpha_dummy_599 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0614
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_597 x u D R S_cls f E) ≠ (nb095_alpha_dummy_600
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0615
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_587
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_589 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_595 D R S_cls E) ≠
        (nb095_alpha_dummy_601 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0620
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_598 x u D R S_cls f E) ≠ (nb095_alpha_dummy_602
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0621
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_595 D R S_cls E) ≠
        (nb095_alpha_dummy_599 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0618
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_598 x u D R S_cls f E) ≠ (nb095_alpha_dummy_600
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0619
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_595 D R S_cls E), (nb095_alpha_dummy_598 x u D R S_cls f E)),
        ((nb095_alpha_dummy_594 D R S_cls E), (nb095_alpha_dummy_597 x u D R S_cls f E)),
        ((nb095_alpha_dummy_593 D R S_cls E), (nb095_alpha_dummy_596 x u D R S_cls f E)),
        ((nb095_alpha_dummy_591 D R S_cls E), (nb095_alpha_dummy_592 x u D R S_cls f E)),
        ((nb095_alpha_dummy_587 D R S_cls E), (nb095_alpha_dummy_589 x u D R S_cls f E)),
        ((nb095_alpha_dummy_588 D R S_cls E), (nb095_alpha_dummy_590 x u D R S_cls f E)),
        ((nb095_alpha_dummy_580 D R S_cls E), (nb095_alpha_dummy_582 x u D R S_cls f E)),
        ((nb095_alpha_dummy_579 D R S_cls E), (nb095_alpha_dummy_581 x u D R S_cls f E)),
        ((nb095_alpha_dummy_585 D R S_cls E), (nb095_alpha_dummy_586 x u D R S_cls f E)),
        ((nb095_alpha_dummy_583 D R S_cls E), (nb095_alpha_dummy_584 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_587 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_589 x u D R S_cls f E))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_587 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_589 x u D R S_cls f E))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_594
        D R S_cls E) ≠ (nb095_alpha_dummy_605 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0624
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_597 x u D R S_cls f E) ≠ (nb095_alpha_dummy_606
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0625
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_594 D R S_cls E) ≠
        (nb095_alpha_dummy_603 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0622
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_597 x u D R S_cls f E) ≠ (nb095_alpha_dummy_604
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0623
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_587
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_589 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_594 D R S_cls E) ≠
        (nb095_alpha_dummy_605 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0624
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_597 x u D R S_cls f E) ≠ (nb095_alpha_dummy_606
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0625
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_594 D R S_cls E) ≠
        (nb095_alpha_dummy_603 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0622
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_597 x u D R S_cls f E) ≠ (nb095_alpha_dummy_604
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0623
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_587
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_589 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_595 D R S_cls E) ≠ (nb095_alpha_dummy_607
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_607;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0628
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_598 x u D R S_cls f E) ≠ (nb095_alpha_dummy_608
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_608;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0629
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_595 D R S_cls E) ≠
        (nb095_alpha_dummy_603 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0626
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_598 x u D R S_cls f E) ≠ (nb095_alpha_dummy_604
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0627
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_595
        D R S_cls E) ≠ (nb095_alpha_dummy_607 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_607;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0628
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_598 x u D R S_cls f E) ≠ (nb095_alpha_dummy_608
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_608;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0629
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_595 D R S_cls E) ≠
        (nb095_alpha_dummy_603 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0626
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_598 x u D R S_cls f E) ≠ (nb095_alpha_dummy_604
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0627
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_587 D R S_cls E) ≠
        (nb095_alpha_dummy_591 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_591;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0610 D R S_cls E)
                                                  0)))) (show
                                        (nb095_alpha_dummy_589 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_592 x u D R S_cls f E) from (by
                                          unfold nb095_alpha_dummy_592;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0611 x u D R S_cls f
                                                    E)
                                                  0)))) (TAlphaVar.here _ _ _)))
                                  (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_591 D R S_cls E),
                                        (nb095_alpha_dummy_592 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_587 D R S_cls E),
                                        (nb095_alpha_dummy_589 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_588 D R S_cls E),
                                        (nb095_alpha_dummy_590 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_580 D R S_cls E),
                                        (nb095_alpha_dummy_582 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_579 D R S_cls E),
                                        (nb095_alpha_dummy_581 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_585 D R S_cls E),
                                        (nb095_alpha_dummy_586 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_583 D R S_cls E),
                                        (nb095_alpha_dummy_584 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_004 D R S_cls E),
                                        (nb095_alpha_dummy_006 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_003 D R S_cls E),
                                        (nb095_alpha_dummy_005 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_001 D R S_cls E), u),
                                      ((nb095_alpha_dummy_002 D R S_cls E), x),
                                      ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_587 D R S_cls E) ≠
                                        (nb095_alpha_dummy_591 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_591;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0610 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_589 x u D R S_cls f E) ≠
                                        (nb095_alpha_dummy_592 x u D R S_cls f E) from (by
                                        unfold nb095_alpha_dummy_592;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0611 x u D R S_cls f E)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_587 D R S_cls E) ≠
        (nb095_alpha_dummy_591 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_591;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0610 D R S_cls E)
                                                  0)))) (show
                                        (nb095_alpha_dummy_589 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_592 x u D R S_cls f E) from (by
                                          unfold nb095_alpha_dummy_592;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0611 x u D R S_cls f
                                                    E)
                                                  0)))) (TAlphaVar.here _ _ _)))
                                  (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_591 D R S_cls E),
                                        (nb095_alpha_dummy_592 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_587 D R S_cls E),
                                        (nb095_alpha_dummy_589 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_588 D R S_cls E),
                                        (nb095_alpha_dummy_590 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_580 D R S_cls E),
                                        (nb095_alpha_dummy_582 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_579 D R S_cls E),
                                        (nb095_alpha_dummy_581 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_585 D R S_cls E),
                                        (nb095_alpha_dummy_586 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_583 D R S_cls E),
                                        (nb095_alpha_dummy_584 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_004 D R S_cls E),
                                        (nb095_alpha_dummy_006 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_003 D R S_cls E),
                                        (nb095_alpha_dummy_005 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_001 D R S_cls E), u),
                                      ((nb095_alpha_dummy_002 D R S_cls E), x),
                                      ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))

@[expose]
noncomputable def nb095_split_alpha_0084 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_580 D R S_cls E), (nb095_alpha_dummy_582 x u D R S_cls f E)),
        ((nb095_alpha_dummy_579 D R S_cls E), (nb095_alpha_dummy_581 x u D R S_cls f E)),
        ((nb095_alpha_dummy_609 D R S_cls E), (nb095_alpha_dummy_610 x u D R S_cls f E)),
        ((nb095_alpha_dummy_583 D R S_cls E), (nb095_alpha_dummy_584 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_580 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_004 D R S_cls E))) (Wff.neg
          (Wff.classEq (Class.cv (nb095_alpha_dummy_579 D R S_cls E))
            (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_580 D R S_cls E)))
              (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E))
          (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))) (Wff.neg
          (Wff.classEq (Class.cv (nb095_alpha_dummy_581 x u D R S_cls f E))
            (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_582 x u D R S_cls f E)))
              (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there
          (show (nb095_alpha_dummy_004 D R S_cls E) ≠ (nb095_alpha_dummy_580 D R S_cls E) from
            (by
              unfold nb095_alpha_dummy_580;
              with_reducible
                exact
                  (Nat.ne_of_lt
                    (mem_lt_freshVar (nb095_support_mem_0630 D R S_cls E) 1)))) (show
            (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
              (nb095_alpha_dummy_582 x u D R S_cls f E) from (by
              unfold nb095_alpha_dummy_582;
              with_reducible
                exact
                  (Nat.ne_of_lt
                    (mem_lt_freshVar (nb095_support_mem_0632 x u D R S_cls f E) 1))))
          (TAlphaVar.there (show
              (nb095_alpha_dummy_004 D R S_cls E) ≠ (nb095_alpha_dummy_579 D R S_cls E) from (by
                unfold nb095_alpha_dummy_579;
                with_reducible
                  exact
                    (Nat.ne_of_lt
                      (mem_lt_freshVar (nb095_support_mem_0630 D R S_cls E) 0)))) (show
              (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
                (nb095_alpha_dummy_581 x u D R S_cls f E) from (by
                unfold nb095_alpha_dummy_581;
                with_reducible
                  exact
                    (Nat.ne_of_lt
                      (mem_lt_freshVar (nb095_support_mem_0632 x u D R S_cls f E) 0))))
            (TAlphaVar.there (show
                (nb095_alpha_dummy_004 D R S_cls E) ≠ (nb095_alpha_dummy_609 D R S_cls E) from
                (by
                  unfold nb095_alpha_dummy_609;
                  with_reducible
                    exact
                      (Nat.ne_of_lt
                        (mem_lt_freshVar (nb095_support_mem_0634 D R S_cls E) 0)))) (show
                (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
                  (nb095_alpha_dummy_610 x u D R S_cls f E) from (by
                  unfold nb095_alpha_dummy_610;
                  with_reducible
                    exact
                      (Nat.ne_of_lt
                        (mem_lt_freshVar (nb095_support_mem_0635 x u D R S_cls f E) 0))))
              (TAlphaVar.there (show (nb095_alpha_dummy_004 D R S_cls E) ≠
                    (nb095_alpha_dummy_583 D R S_cls E) from (by
                    unfold nb095_alpha_dummy_583;
                    with_reducible
                      exact
                        (Nat.ne_of_lt
                          (mem_lt_freshVar (nb095_support_mem_0631 D R S_cls E) 0)))) (show
                  (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
                    (nb095_alpha_dummy_584 x u D R S_cls f E) from (by
                    unfold nb095_alpha_dummy_584;
                    with_reducible
                      exact
                        (Nat.ne_of_lt
                          (mem_lt_freshVar (nb095_support_mem_0633 x u D R S_cls f E)
                            0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb095_alpha_dummy_003 D R S_cls E))).fv ∪
                ((Class.cv (nb095_alpha_dummy_004 D R S_cls E))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))).fv ∪
                ((Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_580 D R S_cls E) ≠
                                        (nb095_alpha_dummy_587 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_587;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0608 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_582 x u D R S_cls f E) ≠
                                        (nb095_alpha_dummy_589 x u D R S_cls f E) from (by
                                        unfold nb095_alpha_dummy_589;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0609 x u D R S_cls f E)
                                                0)))) (TAlphaVar.there (show
                                        (nb095_alpha_dummy_580 D R S_cls E) ≠
        (nb095_alpha_dummy_588 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_588;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0608 D R S_cls E)
                                                  1)))) (show
                                        (nb095_alpha_dummy_582 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_590 x u D R S_cls f E) from (by
                                          unfold nb095_alpha_dummy_590;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0609 x u D R S_cls f
                                                    E)
                                                  1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_580 D R S_cls E) ≠ (nb095_alpha_dummy_613 D R S_cls E) from (by
          unfold nb095_alpha_dummy_613;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0638 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_582 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_614 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_614;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0639 x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_580 D R S_cls E) ≠
        (nb095_alpha_dummy_611 D R S_cls E) from (by
          unfold nb095_alpha_dummy_611;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0636 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_582 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_612 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_612;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0637 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                  (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_580 D R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_582 x u D R S_cls f E))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_587 D R S_cls E) ≠
        (nb095_alpha_dummy_594 D R S_cls E) from (by
          unfold nb095_alpha_dummy_594;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0612
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_589 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_597 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_597;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0613
                    x u D R S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_587 D R S_cls E) ≠
        (nb095_alpha_dummy_593 D R S_cls E) from (by
          unfold nb095_alpha_dummy_593;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0612
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_589 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_596 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_596;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0613
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_587 D R S_cls E) ≠
        (nb095_alpha_dummy_591 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_591;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0610
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_589 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_592 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_592;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0611
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_595 D R S_cls E), (nb095_alpha_dummy_598 x u D R S_cls f E)),
        ((nb095_alpha_dummy_594 D R S_cls E), (nb095_alpha_dummy_597 x u D R S_cls f E)),
        ((nb095_alpha_dummy_593 D R S_cls E), (nb095_alpha_dummy_596 x u D R S_cls f E)),
        ((nb095_alpha_dummy_591 D R S_cls E), (nb095_alpha_dummy_592 x u D R S_cls f E)),
        ((nb095_alpha_dummy_587 D R S_cls E), (nb095_alpha_dummy_589 x u D R S_cls f E)),
        ((nb095_alpha_dummy_588 D R S_cls E), (nb095_alpha_dummy_590 x u D R S_cls f E)),
        ((nb095_alpha_dummy_613 D R S_cls E), (nb095_alpha_dummy_614 x u D R S_cls f E)),
        ((nb095_alpha_dummy_611 D R S_cls E), (nb095_alpha_dummy_612 x u D R S_cls f E)),
        ((nb095_alpha_dummy_580 D R S_cls E), (nb095_alpha_dummy_582 x u D R S_cls f E)),
        ((nb095_alpha_dummy_579 D R S_cls E), (nb095_alpha_dummy_581 x u D R S_cls f E)),
        ((nb095_alpha_dummy_609 D R S_cls E), (nb095_alpha_dummy_610 x u D R S_cls f E)),
        ((nb095_alpha_dummy_583 D R S_cls E), (nb095_alpha_dummy_584 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_594 D R S_cls E) ≠
        (nb095_alpha_dummy_601 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0616
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_597 x u D R S_cls f E) ≠ (nb095_alpha_dummy_602
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0617
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_594 D R S_cls E) ≠
        (nb095_alpha_dummy_599 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0614
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_597 x u D R S_cls f E) ≠ (nb095_alpha_dummy_600
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0615
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_587
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_589 x u D R S_cls f
        E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_595
        D R S_cls E) ≠ (nb095_alpha_dummy_601 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0620
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_598 x u D R S_cls f E) ≠ (nb095_alpha_dummy_602
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0621
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_595 D R S_cls E) ≠
        (nb095_alpha_dummy_599 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0618
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_598 x u D R S_cls f E) ≠ (nb095_alpha_dummy_600
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0619
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_594 D R S_cls E) ≠ (nb095_alpha_dummy_601 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0616
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_597 x u D R S_cls f E) ≠ (nb095_alpha_dummy_602
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0617
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_594 D R S_cls E) ≠
        (nb095_alpha_dummy_599 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0614
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_597 x u D R S_cls f E) ≠ (nb095_alpha_dummy_600
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0615
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_587
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_589 x u D R S_cls f
        E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_595
        D R S_cls E) ≠ (nb095_alpha_dummy_601 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0620
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_598 x u D R S_cls f E) ≠ (nb095_alpha_dummy_602
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0621
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_595 D R S_cls E) ≠
        (nb095_alpha_dummy_599 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0618
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_598 x u D R S_cls f E) ≠ (nb095_alpha_dummy_600
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0619
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_595 D R S_cls E), (nb095_alpha_dummy_598 x u D R S_cls f E)),
        ((nb095_alpha_dummy_594 D R S_cls E), (nb095_alpha_dummy_597 x u D R S_cls f E)),
        ((nb095_alpha_dummy_593 D R S_cls E), (nb095_alpha_dummy_596 x u D R S_cls f E)),
        ((nb095_alpha_dummy_591 D R S_cls E), (nb095_alpha_dummy_592 x u D R S_cls f E)),
        ((nb095_alpha_dummy_587 D R S_cls E), (nb095_alpha_dummy_589 x u D R S_cls f E)),
        ((nb095_alpha_dummy_588 D R S_cls E), (nb095_alpha_dummy_590 x u D R S_cls f E)),
        ((nb095_alpha_dummy_613 D R S_cls E), (nb095_alpha_dummy_614 x u D R S_cls f E)),
        ((nb095_alpha_dummy_611 D R S_cls E), (nb095_alpha_dummy_612 x u D R S_cls f E)),
        ((nb095_alpha_dummy_580 D R S_cls E), (nb095_alpha_dummy_582 x u D R S_cls f E)),
        ((nb095_alpha_dummy_579 D R S_cls E), (nb095_alpha_dummy_581 x u D R S_cls f E)),
        ((nb095_alpha_dummy_609 D R S_cls E), (nb095_alpha_dummy_610 x u D R S_cls f E)),
        ((nb095_alpha_dummy_583 D R S_cls E), (nb095_alpha_dummy_584 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_587 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_589 x u D R S_cls f E))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_587 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_589 x u D R S_cls f E))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_594
        D R S_cls E) ≠ (nb095_alpha_dummy_605 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0624
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_597 x u D R S_cls f E) ≠ (nb095_alpha_dummy_606
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0625
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_594 D R S_cls E) ≠
        (nb095_alpha_dummy_603 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0622
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_597 x u D R S_cls f E) ≠ (nb095_alpha_dummy_604
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0623
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_587
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_589 x u D R S_cls f
        E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_594
        D R S_cls E) ≠ (nb095_alpha_dummy_605 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0624
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_597 x u D R S_cls f E) ≠ (nb095_alpha_dummy_606
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0625
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_594 D R S_cls E) ≠
        (nb095_alpha_dummy_603 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0622
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_597 x u D R S_cls f E) ≠ (nb095_alpha_dummy_604
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0623
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_587
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_589 x u D R S_cls f
        E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_595 D R S_cls E) ≠ (nb095_alpha_dummy_607 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_607;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0628
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_598 x u D R S_cls f E) ≠ (nb095_alpha_dummy_608
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_608;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0629
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_595 D R S_cls E) ≠
        (nb095_alpha_dummy_603 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0626
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_598 x u D R S_cls f E) ≠ (nb095_alpha_dummy_604
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0627
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_595
        D R S_cls E) ≠ (nb095_alpha_dummy_607 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_607;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0628
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_598 x u D R S_cls f E) ≠ (nb095_alpha_dummy_608
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_608;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0629
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_595 D R S_cls E) ≠
        (nb095_alpha_dummy_603 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0626
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_598 x u D R S_cls f E) ≠ (nb095_alpha_dummy_604
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0627
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_587 D R S_cls E) ≠
        (nb095_alpha_dummy_591 D R S_cls E) from (by
          unfold nb095_alpha_dummy_591;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0610 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_589 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_592 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_592;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0611 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_591 D R S_cls E), (nb095_alpha_dummy_592 x u D R S_cls f E)),
        ((nb095_alpha_dummy_587 D R S_cls E), (nb095_alpha_dummy_589 x u D R S_cls f E)),
        ((nb095_alpha_dummy_588 D R S_cls E), (nb095_alpha_dummy_590 x u D R S_cls f E)),
        ((nb095_alpha_dummy_613 D R S_cls E), (nb095_alpha_dummy_614 x u D R S_cls f E)),
        ((nb095_alpha_dummy_611 D R S_cls E), (nb095_alpha_dummy_612 x u D R S_cls f E)),
        ((nb095_alpha_dummy_580 D R S_cls E), (nb095_alpha_dummy_582 x u D R S_cls f E)),
        ((nb095_alpha_dummy_579 D R S_cls E), (nb095_alpha_dummy_581 x u D R S_cls f E)),
        ((nb095_alpha_dummy_609 D R S_cls E), (nb095_alpha_dummy_610 x u D R S_cls f E)),
        ((nb095_alpha_dummy_583 D R S_cls E), (nb095_alpha_dummy_584 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_587 D R S_cls E) ≠
        (nb095_alpha_dummy_591 D R S_cls E) from (by
          unfold nb095_alpha_dummy_591;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0610 D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_589 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_592 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_592;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0611 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_587 D R S_cls E) ≠
        (nb095_alpha_dummy_591 D R S_cls E) from (by
          unfold nb095_alpha_dummy_591;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0610 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_589 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_592 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_592;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0611 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_591 D R S_cls E), (nb095_alpha_dummy_592 x u D R S_cls f E)),
        ((nb095_alpha_dummy_587 D R S_cls E), (nb095_alpha_dummy_589 x u D R S_cls f E)),
        ((nb095_alpha_dummy_588 D R S_cls E), (nb095_alpha_dummy_590 x u D R S_cls f E)),
        ((nb095_alpha_dummy_613 D R S_cls E), (nb095_alpha_dummy_614 x u D R S_cls f E)),
        ((nb095_alpha_dummy_611 D R S_cls E), (nb095_alpha_dummy_612 x u D R S_cls f E)),
        ((nb095_alpha_dummy_580 D R S_cls E), (nb095_alpha_dummy_582 x u D R S_cls f E)),
        ((nb095_alpha_dummy_579 D R S_cls E), (nb095_alpha_dummy_581 x u D R S_cls f E)),
        ((nb095_alpha_dummy_609 D R S_cls E), (nb095_alpha_dummy_610 x u D R S_cls f E)),
        ((nb095_alpha_dummy_583 D R S_cls E), (nb095_alpha_dummy_584 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_580 D R S_cls E) ≠
                                        (nb095_alpha_dummy_587 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_587;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0608 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_582 x u D R S_cls f E) ≠
                                        (nb095_alpha_dummy_589 x u D R S_cls f E) from (by
                                        unfold nb095_alpha_dummy_589;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0609 x u D R S_cls f E)
                                                0)))) (TAlphaVar.there (show
                                        (nb095_alpha_dummy_580 D R S_cls E) ≠
        (nb095_alpha_dummy_588 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_588;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0608 D R S_cls E)
                                                  1)))) (show
                                        (nb095_alpha_dummy_582 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_590 x u D R S_cls f E) from (by
                                          unfold nb095_alpha_dummy_590;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0609 x u D R S_cls f
                                                    E)
                                                  1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_580 D R S_cls E) ≠ (nb095_alpha_dummy_613 D R S_cls E) from (by
          unfold nb095_alpha_dummy_613;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0638 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_582 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_614 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_614;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0639 x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_580 D R S_cls E) ≠
        (nb095_alpha_dummy_611 D R S_cls E) from (by
          unfold nb095_alpha_dummy_611;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0636 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_582 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_612 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_612;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0637 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                  (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_580 D R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_582 x u D R S_cls f E))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_587 D R S_cls E) ≠
        (nb095_alpha_dummy_594 D R S_cls E) from (by
          unfold nb095_alpha_dummy_594;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0612
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_589 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_597 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_597;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0613
                    x u D R S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_587 D R S_cls E) ≠
        (nb095_alpha_dummy_593 D R S_cls E) from (by
          unfold nb095_alpha_dummy_593;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0612
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_589 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_596 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_596;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0613
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_587 D R S_cls E) ≠
        (nb095_alpha_dummy_591 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_591;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0610
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_589 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_592 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_592;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0611
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_595 D R S_cls E), (nb095_alpha_dummy_598 x u D R S_cls f E)),
        ((nb095_alpha_dummy_594 D R S_cls E), (nb095_alpha_dummy_597 x u D R S_cls f E)),
        ((nb095_alpha_dummy_593 D R S_cls E), (nb095_alpha_dummy_596 x u D R S_cls f E)),
        ((nb095_alpha_dummy_591 D R S_cls E), (nb095_alpha_dummy_592 x u D R S_cls f E)),
        ((nb095_alpha_dummy_587 D R S_cls E), (nb095_alpha_dummy_589 x u D R S_cls f E)),
        ((nb095_alpha_dummy_588 D R S_cls E), (nb095_alpha_dummy_590 x u D R S_cls f E)),
        ((nb095_alpha_dummy_613 D R S_cls E), (nb095_alpha_dummy_614 x u D R S_cls f E)),
        ((nb095_alpha_dummy_611 D R S_cls E), (nb095_alpha_dummy_612 x u D R S_cls f E)),
        ((nb095_alpha_dummy_580 D R S_cls E), (nb095_alpha_dummy_582 x u D R S_cls f E)),
        ((nb095_alpha_dummy_579 D R S_cls E), (nb095_alpha_dummy_581 x u D R S_cls f E)),
        ((nb095_alpha_dummy_609 D R S_cls E), (nb095_alpha_dummy_610 x u D R S_cls f E)),
        ((nb095_alpha_dummy_583 D R S_cls E), (nb095_alpha_dummy_584 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_594 D R S_cls E) ≠
        (nb095_alpha_dummy_601 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0616
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_597 x u D R S_cls f E) ≠ (nb095_alpha_dummy_602
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0617
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_594 D R S_cls E) ≠
        (nb095_alpha_dummy_599 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0614
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_597 x u D R S_cls f E) ≠ (nb095_alpha_dummy_600
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0615
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_587
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_589 x u D R S_cls f
        E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_595
        D R S_cls E) ≠ (nb095_alpha_dummy_601 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0620
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_598 x u D R S_cls f E) ≠ (nb095_alpha_dummy_602
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0621
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_595 D R S_cls E) ≠
        (nb095_alpha_dummy_599 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0618
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_598 x u D R S_cls f E) ≠ (nb095_alpha_dummy_600
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0619
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_594 D R S_cls E) ≠ (nb095_alpha_dummy_601 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0616
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_597 x u D R S_cls f E) ≠ (nb095_alpha_dummy_602
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0617
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_594 D R S_cls E) ≠
        (nb095_alpha_dummy_599 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0614
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_597 x u D R S_cls f E) ≠ (nb095_alpha_dummy_600
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0615
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_587
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_589 x u D R S_cls f
        E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_595
        D R S_cls E) ≠ (nb095_alpha_dummy_601 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0620
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_598 x u D R S_cls f E) ≠ (nb095_alpha_dummy_602
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0621
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_595 D R S_cls E) ≠
        (nb095_alpha_dummy_599 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0618
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_598 x u D R S_cls f E) ≠ (nb095_alpha_dummy_600
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0619
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_595 D R S_cls E), (nb095_alpha_dummy_598 x u D R S_cls f E)),
        ((nb095_alpha_dummy_594 D R S_cls E), (nb095_alpha_dummy_597 x u D R S_cls f E)),
        ((nb095_alpha_dummy_593 D R S_cls E), (nb095_alpha_dummy_596 x u D R S_cls f E)),
        ((nb095_alpha_dummy_591 D R S_cls E), (nb095_alpha_dummy_592 x u D R S_cls f E)),
        ((nb095_alpha_dummy_587 D R S_cls E), (nb095_alpha_dummy_589 x u D R S_cls f E)),
        ((nb095_alpha_dummy_588 D R S_cls E), (nb095_alpha_dummy_590 x u D R S_cls f E)),
        ((nb095_alpha_dummy_613 D R S_cls E), (nb095_alpha_dummy_614 x u D R S_cls f E)),
        ((nb095_alpha_dummy_611 D R S_cls E), (nb095_alpha_dummy_612 x u D R S_cls f E)),
        ((nb095_alpha_dummy_580 D R S_cls E), (nb095_alpha_dummy_582 x u D R S_cls f E)),
        ((nb095_alpha_dummy_579 D R S_cls E), (nb095_alpha_dummy_581 x u D R S_cls f E)),
        ((nb095_alpha_dummy_609 D R S_cls E), (nb095_alpha_dummy_610 x u D R S_cls f E)),
        ((nb095_alpha_dummy_583 D R S_cls E), (nb095_alpha_dummy_584 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_587 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_589 x u D R S_cls f E))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_587 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_589 x u D R S_cls f E))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_594
        D R S_cls E) ≠ (nb095_alpha_dummy_605 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0624
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_597 x u D R S_cls f E) ≠ (nb095_alpha_dummy_606
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0625
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_594 D R S_cls E) ≠
        (nb095_alpha_dummy_603 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0622
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_597 x u D R S_cls f E) ≠ (nb095_alpha_dummy_604
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0623
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_587
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_589 x u D R S_cls f
        E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_594
        D R S_cls E) ≠ (nb095_alpha_dummy_605 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0624
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_597 x u D R S_cls f E) ≠ (nb095_alpha_dummy_606
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0625
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_594 D R S_cls E) ≠
        (nb095_alpha_dummy_603 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0622
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_597 x u D R S_cls f E) ≠ (nb095_alpha_dummy_604
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0623
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_587
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_589 x u D R S_cls f
        E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_595 D R S_cls E) ≠ (nb095_alpha_dummy_607 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_607;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0628
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_598 x u D R S_cls f E) ≠ (nb095_alpha_dummy_608
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_608;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0629
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_595 D R S_cls E) ≠
        (nb095_alpha_dummy_603 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0626
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_598 x u D R S_cls f E) ≠ (nb095_alpha_dummy_604
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0627
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_595
        D R S_cls E) ≠ (nb095_alpha_dummy_607 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_607;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0628
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_598 x u D R S_cls f E) ≠ (nb095_alpha_dummy_608
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_608;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0629
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_595 D R S_cls E) ≠
        (nb095_alpha_dummy_603 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0626
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_598 x u D R S_cls f E) ≠ (nb095_alpha_dummy_604
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0627
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_587 D R S_cls E) ≠
        (nb095_alpha_dummy_591 D R S_cls E) from (by
          unfold nb095_alpha_dummy_591;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0610 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_589 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_592 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_592;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0611 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_591 D R S_cls E), (nb095_alpha_dummy_592 x u D R S_cls f E)),
        ((nb095_alpha_dummy_587 D R S_cls E), (nb095_alpha_dummy_589 x u D R S_cls f E)),
        ((nb095_alpha_dummy_588 D R S_cls E), (nb095_alpha_dummy_590 x u D R S_cls f E)),
        ((nb095_alpha_dummy_613 D R S_cls E), (nb095_alpha_dummy_614 x u D R S_cls f E)),
        ((nb095_alpha_dummy_611 D R S_cls E), (nb095_alpha_dummy_612 x u D R S_cls f E)),
        ((nb095_alpha_dummy_580 D R S_cls E), (nb095_alpha_dummy_582 x u D R S_cls f E)),
        ((nb095_alpha_dummy_579 D R S_cls E), (nb095_alpha_dummy_581 x u D R S_cls f E)),
        ((nb095_alpha_dummy_609 D R S_cls E), (nb095_alpha_dummy_610 x u D R S_cls f E)),
        ((nb095_alpha_dummy_583 D R S_cls E), (nb095_alpha_dummy_584 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_587 D R S_cls E) ≠
        (nb095_alpha_dummy_591 D R S_cls E) from (by
          unfold nb095_alpha_dummy_591;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0610 D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_589 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_592 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_592;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0611 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_587 D R S_cls E) ≠
        (nb095_alpha_dummy_591 D R S_cls E) from (by
          unfold nb095_alpha_dummy_591;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0610 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_589 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_592 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_592;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0611 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_591 D R S_cls E), (nb095_alpha_dummy_592 x u D R S_cls f E)),
        ((nb095_alpha_dummy_587 D R S_cls E), (nb095_alpha_dummy_589 x u D R S_cls f E)),
        ((nb095_alpha_dummy_588 D R S_cls E), (nb095_alpha_dummy_590 x u D R S_cls f E)),
        ((nb095_alpha_dummy_613 D R S_cls E), (nb095_alpha_dummy_614 x u D R S_cls f E)),
        ((nb095_alpha_dummy_611 D R S_cls E), (nb095_alpha_dummy_612 x u D R S_cls f E)),
        ((nb095_alpha_dummy_580 D R S_cls E), (nb095_alpha_dummy_582 x u D R S_cls f E)),
        ((nb095_alpha_dummy_579 D R S_cls E), (nb095_alpha_dummy_581 x u D R S_cls f E)),
        ((nb095_alpha_dummy_609 D R S_cls E), (nb095_alpha_dummy_610 x u D R S_cls f E)),
        ((nb095_alpha_dummy_583 D R S_cls E), (nb095_alpha_dummy_584 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_611 D R S_cls E),
                      (nb095_alpha_dummy_612 x u D R S_cls f E)),
                    ((nb095_alpha_dummy_580 D R S_cls E),
                      (nb095_alpha_dummy_582 x u D R S_cls f E)),
                    ((nb095_alpha_dummy_579 D R S_cls E),
                      (nb095_alpha_dummy_581 x u D R S_cls f E)),
                    ((nb095_alpha_dummy_609 D R S_cls E),
                      (nb095_alpha_dummy_610 x u D R S_cls f E)),
                    ((nb095_alpha_dummy_583 D R S_cls E),
                      (nb095_alpha_dummy_584 x u D R S_cls f E)),
                    ((nb095_alpha_dummy_004 D R S_cls E),
                      (nb095_alpha_dummy_006 x u D R S_cls f E)),
                    ((nb095_alpha_dummy_003 D R S_cls E),
                      (nb095_alpha_dummy_005 x u D R S_cls f E)),
                    ((nb095_alpha_dummy_001 D R S_cls E), u),
                    ((nb095_alpha_dummy_002 D R S_cls E), x),
                    ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_ccompl (syn_csn (syn_c0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

theorem nb095_focused_notmem_0052 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_617 D R S_cls E) ∉ R.fv :=
  by
  change
    freshVar
        ((R).fv ∪ ((syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))))).fv)
        0 ∉
      R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (hu))

theorem nb095_focused_notmem_0053 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_618 x D R) ∉ R.fv :=
  by
  change
    freshVar
        ((R).fv ∪ ((syn_cxp (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))))).fv)
        0 ∉
      R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (hu))

theorem nb095_focused_notmem_0054 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_615 D R S_cls E) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_cnin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))))).fv ∪
          ((syn_cnin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin R
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0055 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_616 x D R) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_cnin R (syn_cxp (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (Class.cv x))))))).fv ∪ ((syn_cnin R (syn_cxp (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (Class.cv x))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin R
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_compact_envfresh_0290 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_R_f : f ∉ R.fv) (dv_R_u : u ∉ R.fv)
    (dv_R_x : x ∉ R.fv) :
    TEnvFresh
      [((nb095_alpha_dummy_617 D R S_cls E), (nb095_alpha_dummy_618 x D R)),
        ((nb095_alpha_dummy_615 D R S_cls E), (nb095_alpha_dummy_616 x D R)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      R.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb095_alpha_dummy_617 D R S_cls E) (nb095_alpha_dummy_618 x D R)
      (nb095_focused_notmem_0052 D R S_cls E) (nb095_focused_notmem_0053 x D R)
      (TEnvFresh.consFresh (nb095_alpha_dummy_615 D R S_cls E)
        (nb095_alpha_dummy_616 x D R) (nb095_focused_notmem_0054 D R S_cls E)
        (nb095_focused_notmem_0055 x D R)
        (TEnvFresh.consFresh (nb095_alpha_dummy_004 D R S_cls E)
          (nb095_alpha_dummy_006 x u D R S_cls f E) (nb095_focused_notmem_0050 D R S_cls E)
          (nb095_focused_notmem_0051 x u D R S_cls f E)
          (TEnvFresh.consFresh (nb095_alpha_dummy_003 D R S_cls E)
            (nb095_alpha_dummy_005 x u D R S_cls f E) (nb095_focused_notmem_0046 D R S_cls E)
            (nb095_focused_notmem_0047 x u D R S_cls f E)
            (TEnvFresh.consFresh (nb095_alpha_dummy_001 D R S_cls E) u
              (nb095_focused_notmem_0018 D R S_cls E) dv_R_u
              (TEnvFresh.consFresh (nb095_alpha_dummy_002 D R S_cls E) x
                (nb095_focused_notmem_0019 D R S_cls E) dv_R_x
                (TEnvFresh.consFresh (nb095_alpha_dummy_000 D R S_cls E) f
                  (nb095_focused_notmem_0020 D R S_cls E) dv_R_f (TEnvFresh.nil R.fv))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
