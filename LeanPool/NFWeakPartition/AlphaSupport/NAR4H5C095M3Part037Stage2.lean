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

/-- Checked nominal proof certificate identified upstream as `nb095_wpp_refl_0275`. -/
@[expose]
noncomputable def nb095WppRefl0275 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_R_f : f ∉ R.fv) (dv_R_u : u ∉ R.fv)
    (dv_R_x : x ∉ R.fv) :
    TReflOn
      [((nb095AlphaDummy250 D R S_cls E), (nb095AlphaDummy252 x R)),
        ((nb095AlphaDummy249 D R S_cls E), (nb095AlphaDummy251 x R)),
        ((nb095AlphaDummy247 D R S_cls E), (nb095AlphaDummy248 x D R)),
        ((nb095AlphaDummy245 D R S_cls E), (nb095AlphaDummy246 x D R)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      ((synCcnv (synCdif R (synCid)))).fv :=
  TEnvFresh.reflOn (nb095_compact_envfresh_0282 x u D R S_cls f E dv_R_f dv_R_u dv_R_x)

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0083`. -/
@[expose]
noncomputable def nb095SplitAlpha0083 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy585 D R S_cls E), (nb095AlphaDummy586 x u D R S_cls f E)),
        ((nb095AlphaDummy583 D R S_cls E), (nb095AlphaDummy584 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy585 D R S_cls E))
          (Class.cab (nb095AlphaDummy579 D R S_cls E)
            (synWrex (nb095AlphaDummy580 D R S_cls E)
              (Class.cv (nb095AlphaDummy003 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy579 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy580 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy585 D R S_cls E))
            (Class.cab (nb095AlphaDummy579 D R S_cls E)
              (synWrex (nb095AlphaDummy580 D R S_cls E)
                (Class.cv (nb095AlphaDummy003 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy579 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy580 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy586 x u D R S_cls f E))
          (Class.cab (nb095AlphaDummy581 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy582 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy005 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy581 x u D R S_cls f E))
                (synCphi (Class.cv (nb095AlphaDummy582 x u D R S_cls f E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy586 x u D R S_cls f E))
            (Class.cab (nb095AlphaDummy581 x u D R S_cls f E)
              (synWrex (nb095AlphaDummy582 x u D R S_cls f E)
                (Class.cv (nb095AlphaDummy005 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095AlphaDummy581 x u D R S_cls f E))
                  (synCphi (Class.cv (nb095AlphaDummy582 x u D R S_cls f E))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095AlphaDummy003 D R S_cls E) ≠
                      (nb095AlphaDummy580 D R S_cls E) from (by
                      unfold nb095AlphaDummy580;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0602 D R S_cls E) 1)))) (show
                    (nb095AlphaDummy005 x u D R S_cls f E) ≠
                      (nb095AlphaDummy582 x u D R S_cls f E) from (by
                      unfold nb095AlphaDummy582;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0604 x u D R S_cls f E)
                              1)))) (TAlphaVar.there (show (nb095AlphaDummy003 D R S_cls E) ≠
                        (nb095AlphaDummy579 D R S_cls E) from (by
                        unfold nb095AlphaDummy579;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0602 D R S_cls E) 0)))) (show
                      (nb095AlphaDummy005 x u D R S_cls f E) ≠
                        (nb095AlphaDummy581 x u D R S_cls f E) from (by
                        unfold nb095AlphaDummy581;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0604 x u D R S_cls f E)
                                0)))) (TAlphaVar.there (show
                        (nb095AlphaDummy003 D R S_cls E) ≠
                          (nb095AlphaDummy585 D R S_cls E) from (by
                          unfold nb095AlphaDummy585;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0606 D R S_cls E)
                                  0)))) (show (nb095AlphaDummy005 x u D R S_cls f E) ≠
                          (nb095AlphaDummy586 x u D R S_cls f E) from (by
                          unfold nb095AlphaDummy586;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar
                                  (nb095_support_mem_0607 x u D R S_cls f E) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy003 D R S_cls E) ≠
                            (nb095AlphaDummy583 D R S_cls E) from (by
                            unfold nb095AlphaDummy583;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0603 D R S_cls E)
                                    0)))) (show (nb095AlphaDummy005 x u D R S_cls f E) ≠
                            (nb095AlphaDummy584 x u D R S_cls f E) from (by
                            unfold nb095AlphaDummy584;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar
                                    (nb095_support_mem_0605 x u D R S_cls f E) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪ ((synCin R
                                        (synCxp (synCin D
        (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv
        (nb095AlphaDummy002 D R S_cls E))))) (synCin D
        (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv
        (nb095AlphaDummy002 D R S_cls E)))))))).fv ∪ ((synCin S_cls (synCxp (synCin E
        (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv
        (nb095AlphaDummy001 D R S_cls E))))) (synCin E
        (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv
        (nb095AlphaDummy001 D R S_cls E)))))))).fv ∪ ((synCin D
                                    (synCima (synCcnv (synCdif R (synCid))) (synCsn
                                        (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv ∪
                              ((synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                                    (synCsn (Class.cv
                                        (nb095AlphaDummy001 D R S_cls E)))))).fv)
                            (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((synCin R
                                        (synCxp (synCin D
        (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))) (synCin D
        (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))))).fv ∪
                                  ((synCin S_cls (synCxp (synCin E
        (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))) (synCin E
        (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))))).fv ∪
                                ((synCin D (synCima (synCcnv (synCdif R (synCid)))
                                      (synCsn (Class.cv x))))).fv ∪ ((synCin E
                                  (synCima (synCcnv (synCdif S_cls (synCid)))
                                    (synCsn (Class.cv u))))).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095AlphaDummy003 D R S_cls E))).fv ∪
                      ((Class.cv (nb095AlphaDummy004 D R S_cls E))).fv) (by decide))
                  (freshVar_injective
                    (((Class.cv (nb095AlphaDummy005 x u D R S_cls f E))).fv ∪
                      ((Class.cv (nb095AlphaDummy006 x u D R S_cls f E))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095AlphaDummy580 D R S_cls E) ≠
                              (nb095AlphaDummy587 D R S_cls E) from (by
                              unfold nb095AlphaDummy587;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0608 D R S_cls E)
                                      0)))) (show (nb095AlphaDummy582 x u D R S_cls f E) ≠
                              (nb095AlphaDummy589 x u D R S_cls f E) from (by
                              unfold nb095AlphaDummy589;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb095_support_mem_0609 x u D R S_cls f E) 0))))
                          (TAlphaVar.there (show (nb095AlphaDummy580 D R S_cls E) ≠
                                (nb095AlphaDummy588 D R S_cls E) from (by
                                unfold nb095AlphaDummy588;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0608 D R S_cls E) 1)))) (show
                              (nb095AlphaDummy582 x u D R S_cls f E) ≠
                                (nb095AlphaDummy590 x u D R S_cls f E) from (by
                                unfold nb095AlphaDummy590;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0609 x u D R S_cls f E) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095AlphaDummy580 D R S_cls E))).fv) (by decide))
                          (freshVar_injective
                            (((Class.cv (nb095AlphaDummy582 x u D R S_cls f E))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy587 D R S_cls E) ≠
        (nb095AlphaDummy594 D R S_cls E) from (by
          unfold nb095AlphaDummy594;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0612 D R S_cls
                    E)
                  1)))) (show (nb095AlphaDummy589 x u D R S_cls f E) ≠
        (nb095AlphaDummy597 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy597;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0613 x u D R
                    S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy587 D R S_cls E) ≠
        (nb095AlphaDummy593 D R S_cls E) from (by
          unfold nb095AlphaDummy593;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0612 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy589 x u D R S_cls f E) ≠
        (nb095AlphaDummy596 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy596;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0613 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy587 D R S_cls E) ≠
        (nb095AlphaDummy591 D R S_cls E) from (by
          unfold nb095AlphaDummy591;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0610 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy589 x u D R S_cls f E) ≠
        (nb095AlphaDummy592 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy592;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0611 x u D
                    R S_cls f E)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy595 D R S_cls E), (nb095AlphaDummy598 x u D R S_cls f E)),
        ((nb095AlphaDummy594 D R S_cls E), (nb095AlphaDummy597 x u D R S_cls f E)),
        ((nb095AlphaDummy593 D R S_cls E), (nb095AlphaDummy596 x u D R S_cls f E)),
        ((nb095AlphaDummy591 D R S_cls E), (nb095AlphaDummy592 x u D R S_cls f E)),
        ((nb095AlphaDummy587 D R S_cls E), (nb095AlphaDummy589 x u D R S_cls f E)),
        ((nb095AlphaDummy588 D R S_cls E), (nb095AlphaDummy590 x u D R S_cls f E)),
        ((nb095AlphaDummy580 D R S_cls E), (nb095AlphaDummy582 x u D R S_cls f E)),
        ((nb095AlphaDummy579 D R S_cls E), (nb095AlphaDummy581 x u D R S_cls f E)),
        ((nb095AlphaDummy585 D R S_cls E), (nb095AlphaDummy586 x u D R S_cls f E)),
        ((nb095AlphaDummy583 D R S_cls E), (nb095AlphaDummy584 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy594
        D R S_cls E) ≠ (nb095AlphaDummy601 D R S_cls E) from (by
          unfold
            nb095AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0616
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy597 x u D R S_cls f E) ≠ (nb095AlphaDummy602
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0617
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy594 D R S_cls E) ≠
        (nb095AlphaDummy599 D R S_cls E) from (by
          unfold
            nb095AlphaDummy599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0614
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy597 x u D R S_cls f E) ≠ (nb095AlphaDummy600
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0615
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy587
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy589 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy595 D R S_cls E) ≠
        (nb095AlphaDummy601 D R S_cls E) from (by
          unfold
            nb095AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0620
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy598 x u D R S_cls f E) ≠ (nb095AlphaDummy602
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0621
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy595 D R S_cls E) ≠
        (nb095AlphaDummy599 D R S_cls E) from (by
          unfold
            nb095AlphaDummy599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0618
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy598 x u D R S_cls f E) ≠ (nb095AlphaDummy600
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy600;
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
        (TAlphaVar.there (show (nb095AlphaDummy594 D R S_cls E) ≠ (nb095AlphaDummy601
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0616
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy597 x u D R S_cls f E) ≠ (nb095AlphaDummy602
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0617
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy594 D R S_cls E) ≠
        (nb095AlphaDummy599 D R S_cls E) from (by
          unfold
            nb095AlphaDummy599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0614
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy597 x u D R S_cls f E) ≠ (nb095AlphaDummy600
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0615
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy587
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy589 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy595 D R S_cls E) ≠
        (nb095AlphaDummy601 D R S_cls E) from (by
          unfold
            nb095AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0620
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy598 x u D R S_cls f E) ≠ (nb095AlphaDummy602
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0621
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy595 D R S_cls E) ≠
        (nb095AlphaDummy599 D R S_cls E) from (by
          unfold
            nb095AlphaDummy599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0618
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy598 x u D R S_cls f E) ≠ (nb095AlphaDummy600
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0619
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy595 D R S_cls E), (nb095AlphaDummy598 x u D R S_cls f E)),
        ((nb095AlphaDummy594 D R S_cls E), (nb095AlphaDummy597 x u D R S_cls f E)),
        ((nb095AlphaDummy593 D R S_cls E), (nb095AlphaDummy596 x u D R S_cls f E)),
        ((nb095AlphaDummy591 D R S_cls E), (nb095AlphaDummy592 x u D R S_cls f E)),
        ((nb095AlphaDummy587 D R S_cls E), (nb095AlphaDummy589 x u D R S_cls f E)),
        ((nb095AlphaDummy588 D R S_cls E), (nb095AlphaDummy590 x u D R S_cls f E)),
        ((nb095AlphaDummy580 D R S_cls E), (nb095AlphaDummy582 x u D R S_cls f E)),
        ((nb095AlphaDummy579 D R S_cls E), (nb095AlphaDummy581 x u D R S_cls f E)),
        ((nb095AlphaDummy585 D R S_cls E), (nb095AlphaDummy586 x u D R S_cls f E)),
        ((nb095AlphaDummy583 D R S_cls E), (nb095AlphaDummy584 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy587 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy589 x u D R S_cls f E))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy587 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy589 x u D R S_cls f E))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy594
        D R S_cls E) ≠ (nb095AlphaDummy605 D R S_cls E) from (by
          unfold
            nb095AlphaDummy605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0624
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy597 x u D R S_cls f E) ≠ (nb095AlphaDummy606
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0625
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy594 D R S_cls E) ≠
        (nb095AlphaDummy603 D R S_cls E) from (by
          unfold
            nb095AlphaDummy603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0622
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy597 x u D R S_cls f E) ≠ (nb095AlphaDummy604
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0623
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy587
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy589 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy594 D R S_cls E) ≠
        (nb095AlphaDummy605 D R S_cls E) from (by
          unfold
            nb095AlphaDummy605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0624
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy597 x u D R S_cls f E) ≠ (nb095AlphaDummy606
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0625
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy594 D R S_cls E) ≠
        (nb095AlphaDummy603 D R S_cls E) from (by
          unfold
            nb095AlphaDummy603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0622
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy597 x u D R S_cls f E) ≠ (nb095AlphaDummy604
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0623
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy587
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy589 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy595 D R S_cls E) ≠ (nb095AlphaDummy607
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy607;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0628
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy598 x u D R S_cls f E) ≠ (nb095AlphaDummy608
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy608;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0629
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy595 D R S_cls E) ≠
        (nb095AlphaDummy603 D R S_cls E) from (by
          unfold
            nb095AlphaDummy603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0626
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy598 x u D R S_cls f E) ≠ (nb095AlphaDummy604
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0627
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy595
        D R S_cls E) ≠ (nb095AlphaDummy607 D R S_cls E) from (by
          unfold
            nb095AlphaDummy607;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0628
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy598 x u D R S_cls f E) ≠ (nb095AlphaDummy608
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy608;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0629
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy595 D R S_cls E) ≠
        (nb095AlphaDummy603 D R S_cls E) from (by
          unfold
            nb095AlphaDummy603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0626
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy598 x u D R S_cls f E) ≠ (nb095AlphaDummy604
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy604;
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
                                      (nb095AlphaDummy587 D R S_cls E) ≠
                                        (nb095AlphaDummy591 D R S_cls E) from (by
                                        unfold nb095AlphaDummy591;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0610 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy589 x u D R S_cls f E) ≠
                                        (nb095AlphaDummy592 x u D R S_cls f E) from (by
                                        unfold nb095AlphaDummy592;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0611 x u D R S_cls f E)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy591 D R S_cls E),
                                      (nb095AlphaDummy592 x u D R S_cls f E)),
                                    ((nb095AlphaDummy587 D R S_cls E),
                                      (nb095AlphaDummy589 x u D R S_cls f E)),
                                    ((nb095AlphaDummy588 D R S_cls E),
                                      (nb095AlphaDummy590 x u D R S_cls f E)),
                                    ((nb095AlphaDummy580 D R S_cls E),
                                      (nb095AlphaDummy582 x u D R S_cls f E)),
                                    ((nb095AlphaDummy579 D R S_cls E),
                                      (nb095AlphaDummy581 x u D R S_cls f E)),
                                    ((nb095AlphaDummy585 D R S_cls E),
                                      (nb095AlphaDummy586 x u D R S_cls f E)),
                                    ((nb095AlphaDummy583 D R S_cls E),
                                      (nb095AlphaDummy584 x u D R S_cls f E)),
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
                                    (nb095AlphaDummy587 D R S_cls E) ≠
                                      (nb095AlphaDummy591 D R S_cls E) from (by
                                      unfold nb095AlphaDummy591;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0610 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy589 x u D R S_cls f E) ≠
                                      (nb095AlphaDummy592 x u D R S_cls f E) from (by
                                      unfold nb095AlphaDummy592;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0611 x u D R S_cls f E)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy587 D R S_cls E) ≠
                                        (nb095AlphaDummy591 D R S_cls E) from (by
                                        unfold nb095AlphaDummy591;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0610 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy589 x u D R S_cls f E) ≠
                                        (nb095AlphaDummy592 x u D R S_cls f E) from (by
                                        unfold nb095AlphaDummy592;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0611 x u D R S_cls f E)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy591 D R S_cls E),
                                      (nb095AlphaDummy592 x u D R S_cls f E)),
                                    ((nb095AlphaDummy587 D R S_cls E),
                                      (nb095AlphaDummy589 x u D R S_cls f E)),
                                    ((nb095AlphaDummy588 D R S_cls E),
                                      (nb095AlphaDummy590 x u D R S_cls f E)),
                                    ((nb095AlphaDummy580 D R S_cls E),
                                      (nb095AlphaDummy582 x u D R S_cls f E)),
                                    ((nb095AlphaDummy579 D R S_cls E),
                                      (nb095AlphaDummy581 x u D R S_cls f E)),
                                    ((nb095AlphaDummy585 D R S_cls E),
                                      (nb095AlphaDummy586 x u D R S_cls f E)),
                                    ((nb095AlphaDummy583 D R S_cls E),
                                      (nb095AlphaDummy584 x u D R S_cls f E)),
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
                  (TAlphaVar.there (show (nb095AlphaDummy003 D R S_cls E) ≠
                        (nb095AlphaDummy580 D R S_cls E) from (by
                        unfold nb095AlphaDummy580;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0602 D R S_cls E) 1)))) (show
                      (nb095AlphaDummy005 x u D R S_cls f E) ≠
                        (nb095AlphaDummy582 x u D R S_cls f E) from (by
                        unfold nb095AlphaDummy582;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0604 x u D R S_cls f E)
                                1)))) (TAlphaVar.there (show
                        (nb095AlphaDummy003 D R S_cls E) ≠
                          (nb095AlphaDummy579 D R S_cls E) from (by
                          unfold nb095AlphaDummy579;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0602 D R S_cls E)
                                  0)))) (show (nb095AlphaDummy005 x u D R S_cls f E) ≠
                          (nb095AlphaDummy581 x u D R S_cls f E) from (by
                          unfold nb095AlphaDummy581;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar
                                  (nb095_support_mem_0604 x u D R S_cls f E) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy003 D R S_cls E) ≠
                            (nb095AlphaDummy585 D R S_cls E) from (by
                            unfold nb095AlphaDummy585;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0606 D R S_cls E)
                                    0)))) (show (nb095AlphaDummy005 x u D R S_cls f E) ≠
                            (nb095AlphaDummy586 x u D R S_cls f E) from (by
                            unfold nb095AlphaDummy586;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar
                                    (nb095_support_mem_0607 x u D R S_cls f E) 0))))
                        (TAlphaVar.there (show (nb095AlphaDummy003 D R S_cls E) ≠
                              (nb095AlphaDummy583 D R S_cls E) from (by
                              unfold nb095AlphaDummy583;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0603 D R S_cls E)
                                      0)))) (show (nb095AlphaDummy005 x u D R S_cls f E) ≠
                              (nb095AlphaDummy584 x u D R S_cls f E) from (by
                              unfold nb095AlphaDummy584;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb095_support_mem_0605 x u D R S_cls f E) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪ ((synCin R
        (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv
        (nb095AlphaDummy002 D R S_cls E))))) (synCin D
        (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv
        (nb095AlphaDummy002 D R S_cls E)))))))).fv ∪ ((synCin S_cls (synCxp (synCin E
        (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv
        (nb095AlphaDummy001 D R S_cls E))))) (synCin E (synCima
        (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv
        (nb095AlphaDummy001 D R S_cls E)))))))).fv ∪ ((synCin D
                                      (synCima (synCcnv (synCdif R (synCid))) (synCsn
        (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv ∪ ((synCin E
                                    (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn
                                        (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv)
                              (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((synCin R
        (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))))).fv ∪
                                    ((synCin S_cls (synCxp (synCin E (synCima
        (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))) (synCin E (synCima
        (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))))).fv ∪ ((synCin D
                                      (synCima (synCcnv (synCdif R (synCid)))
                                        (synCsn (Class.cv x))))).fv ∪ ((synCin E
                                    (synCima (synCcnv (synCdif S_cls (synCid)))
                                      (synCsn (Class.cv u))))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095AlphaDummy003 D R S_cls E))).fv ∪
                        ((Class.cv (nb095AlphaDummy004 D R S_cls E))).fv) (by decide))
                    (freshVar_injective
                      (((Class.cv (nb095AlphaDummy005 x u D R S_cls f E))).fv ∪
                        ((Class.cv (nb095AlphaDummy006 x u D R S_cls f E))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy580 D R S_cls E) ≠
                                (nb095AlphaDummy587 D R S_cls E) from (by
                                unfold nb095AlphaDummy587;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0608 D R S_cls E) 0)))) (show
                              (nb095AlphaDummy582 x u D R S_cls f E) ≠
                                (nb095AlphaDummy589 x u D R S_cls f E) from (by
                                unfold nb095AlphaDummy589;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0609 x u D R S_cls f E) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy580 D R S_cls E) ≠
                                  (nb095AlphaDummy588 D R S_cls E) from (by
                                  unfold nb095AlphaDummy588;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0608 D R S_cls E) 1)))) (show
                                (nb095AlphaDummy582 x u D R S_cls f E) ≠
                                  (nb095AlphaDummy590 x u D R S_cls f E) from (by
                                  unfold nb095AlphaDummy590;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0609 x u D R S_cls f E) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095AlphaDummy580 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095AlphaDummy582 x u D R S_cls f E))).fv)
                              (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                          (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy587 D R S_cls E) ≠ (nb095AlphaDummy594 D R S_cls E) from (by
          unfold nb095AlphaDummy594;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0612 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy589 x u D R S_cls f E) ≠
        (nb095AlphaDummy597 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy597;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0613 x u D R
                    S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy587 D R S_cls E) ≠
        (nb095AlphaDummy593 D R S_cls E) from (by
          unfold nb095AlphaDummy593;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0612 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy589 x u D R S_cls f E) ≠
        (nb095AlphaDummy596 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy596;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0613 x u D
                    R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy587 D R S_cls E) ≠
        (nb095AlphaDummy591 D R S_cls E) from (by
          unfold nb095AlphaDummy591;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0610 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy589 x u D R S_cls f E) ≠
        (nb095AlphaDummy592 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy592;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0611 x u
                    D R S_cls f E)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy595 D R S_cls E), (nb095AlphaDummy598 x u D R S_cls f E)),
        ((nb095AlphaDummy594 D R S_cls E), (nb095AlphaDummy597 x u D R S_cls f E)),
        ((nb095AlphaDummy593 D R S_cls E), (nb095AlphaDummy596 x u D R S_cls f E)),
        ((nb095AlphaDummy591 D R S_cls E), (nb095AlphaDummy592 x u D R S_cls f E)),
        ((nb095AlphaDummy587 D R S_cls E), (nb095AlphaDummy589 x u D R S_cls f E)),
        ((nb095AlphaDummy588 D R S_cls E), (nb095AlphaDummy590 x u D R S_cls f E)),
        ((nb095AlphaDummy580 D R S_cls E), (nb095AlphaDummy582 x u D R S_cls f E)),
        ((nb095AlphaDummy579 D R S_cls E), (nb095AlphaDummy581 x u D R S_cls f E)),
        ((nb095AlphaDummy585 D R S_cls E), (nb095AlphaDummy586 x u D R S_cls f E)),
        ((nb095AlphaDummy583 D R S_cls E), (nb095AlphaDummy584 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy594
        D R S_cls E) ≠ (nb095AlphaDummy601 D R S_cls E) from (by
          unfold
            nb095AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0616
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy597 x u D R S_cls f E) ≠ (nb095AlphaDummy602
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0617
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy594 D R S_cls E) ≠
        (nb095AlphaDummy599 D R S_cls E) from (by
          unfold
            nb095AlphaDummy599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0614
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy597 x u D R S_cls f E) ≠ (nb095AlphaDummy600
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0615
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy587
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy589 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy595 D R S_cls E) ≠
        (nb095AlphaDummy601 D R S_cls E) from (by
          unfold
            nb095AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0620
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy598 x u D R S_cls f E) ≠ (nb095AlphaDummy602
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0621
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy595 D R S_cls E) ≠
        (nb095AlphaDummy599 D R S_cls E) from (by
          unfold
            nb095AlphaDummy599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0618
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy598 x u D R S_cls f E) ≠ (nb095AlphaDummy600
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy600;
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
        (TAlphaVar.there (show (nb095AlphaDummy594 D R S_cls E) ≠ (nb095AlphaDummy601
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0616
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy597 x u D R S_cls f E) ≠ (nb095AlphaDummy602
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0617
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy594 D R S_cls E) ≠
        (nb095AlphaDummy599 D R S_cls E) from (by
          unfold
            nb095AlphaDummy599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0614
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy597 x u D R S_cls f E) ≠ (nb095AlphaDummy600
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0615
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy587
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy589 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy595 D R S_cls E) ≠
        (nb095AlphaDummy601 D R S_cls E) from (by
          unfold
            nb095AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0620
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy598 x u D R S_cls f E) ≠ (nb095AlphaDummy602
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0621
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy595 D R S_cls E) ≠
        (nb095AlphaDummy599 D R S_cls E) from (by
          unfold
            nb095AlphaDummy599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0618
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy598 x u D R S_cls f E) ≠ (nb095AlphaDummy600
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0619
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy595 D R S_cls E), (nb095AlphaDummy598 x u D R S_cls f E)),
        ((nb095AlphaDummy594 D R S_cls E), (nb095AlphaDummy597 x u D R S_cls f E)),
        ((nb095AlphaDummy593 D R S_cls E), (nb095AlphaDummy596 x u D R S_cls f E)),
        ((nb095AlphaDummy591 D R S_cls E), (nb095AlphaDummy592 x u D R S_cls f E)),
        ((nb095AlphaDummy587 D R S_cls E), (nb095AlphaDummy589 x u D R S_cls f E)),
        ((nb095AlphaDummy588 D R S_cls E), (nb095AlphaDummy590 x u D R S_cls f E)),
        ((nb095AlphaDummy580 D R S_cls E), (nb095AlphaDummy582 x u D R S_cls f E)),
        ((nb095AlphaDummy579 D R S_cls E), (nb095AlphaDummy581 x u D R S_cls f E)),
        ((nb095AlphaDummy585 D R S_cls E), (nb095AlphaDummy586 x u D R S_cls f E)),
        ((nb095AlphaDummy583 D R S_cls E), (nb095AlphaDummy584 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy587 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy589 x u D R S_cls f E))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy587 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy589 x u D R S_cls f E))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy594
        D R S_cls E) ≠ (nb095AlphaDummy605 D R S_cls E) from (by
          unfold
            nb095AlphaDummy605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0624
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy597 x u D R S_cls f E) ≠ (nb095AlphaDummy606
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0625
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy594 D R S_cls E) ≠
        (nb095AlphaDummy603 D R S_cls E) from (by
          unfold
            nb095AlphaDummy603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0622
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy597 x u D R S_cls f E) ≠ (nb095AlphaDummy604
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0623
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy587
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy589 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy594 D R S_cls E) ≠
        (nb095AlphaDummy605 D R S_cls E) from (by
          unfold
            nb095AlphaDummy605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0624
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy597 x u D R S_cls f E) ≠ (nb095AlphaDummy606
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0625
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy594 D R S_cls E) ≠
        (nb095AlphaDummy603 D R S_cls E) from (by
          unfold
            nb095AlphaDummy603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0622
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy597 x u D R S_cls f E) ≠ (nb095AlphaDummy604
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0623
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy587
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy589 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy595 D R S_cls E) ≠ (nb095AlphaDummy607
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy607;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0628
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy598 x u D R S_cls f E) ≠ (nb095AlphaDummy608
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy608;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0629
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy595 D R S_cls E) ≠
        (nb095AlphaDummy603 D R S_cls E) from (by
          unfold
            nb095AlphaDummy603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0626
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy598 x u D R S_cls f E) ≠ (nb095AlphaDummy604
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy604;
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy595
        D R S_cls E) ≠ (nb095AlphaDummy607 D R S_cls E) from (by
          unfold
            nb095AlphaDummy607;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0628
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy598 x u D R S_cls f E) ≠ (nb095AlphaDummy608
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy608;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0629
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy595 D R S_cls E) ≠
        (nb095AlphaDummy603 D R S_cls E) from (by
          unfold
            nb095AlphaDummy603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0626
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy598 x u D R S_cls f E) ≠ (nb095AlphaDummy604
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy604;
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
                                        (nb095AlphaDummy587 D R S_cls E) ≠
        (nb095AlphaDummy591 D R S_cls E) from (by
                                          unfold nb095AlphaDummy591;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0610 D R S_cls E)
                                                  0)))) (show
                                        (nb095AlphaDummy589 x u D R S_cls f E) ≠
        (nb095AlphaDummy592 x u D R S_cls f E) from (by
                                          unfold nb095AlphaDummy592;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0611 x u D R S_cls f
                                                    E)
                                                  0)))) (TAlphaVar.here _ _ _)))
                                  (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy591 D R S_cls E),
                                        (nb095AlphaDummy592 x u D R S_cls f E)),
                                      ((nb095AlphaDummy587 D R S_cls E),
                                        (nb095AlphaDummy589 x u D R S_cls f E)),
                                      ((nb095AlphaDummy588 D R S_cls E),
                                        (nb095AlphaDummy590 x u D R S_cls f E)),
                                      ((nb095AlphaDummy580 D R S_cls E),
                                        (nb095AlphaDummy582 x u D R S_cls f E)),
                                      ((nb095AlphaDummy579 D R S_cls E),
                                        (nb095AlphaDummy581 x u D R S_cls f E)),
                                      ((nb095AlphaDummy585 D R S_cls E),
                                        (nb095AlphaDummy586 x u D R S_cls f E)),
                                      ((nb095AlphaDummy583 D R S_cls E),
                                        (nb095AlphaDummy584 x u D R S_cls f E)),
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
                                      (nb095AlphaDummy587 D R S_cls E) ≠
                                        (nb095AlphaDummy591 D R S_cls E) from (by
                                        unfold nb095AlphaDummy591;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0610 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy589 x u D R S_cls f E) ≠
                                        (nb095AlphaDummy592 x u D R S_cls f E) from (by
                                        unfold nb095AlphaDummy592;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0611 x u D R S_cls f E)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy587 D R S_cls E) ≠
        (nb095AlphaDummy591 D R S_cls E) from (by
                                          unfold nb095AlphaDummy591;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0610 D R S_cls E)
                                                  0)))) (show
                                        (nb095AlphaDummy589 x u D R S_cls f E) ≠
        (nb095AlphaDummy592 x u D R S_cls f E) from (by
                                          unfold nb095AlphaDummy592;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0611 x u D R S_cls f
                                                    E)
                                                  0)))) (TAlphaVar.here _ _ _)))
                                  (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy591 D R S_cls E),
                                        (nb095AlphaDummy592 x u D R S_cls f E)),
                                      ((nb095AlphaDummy587 D R S_cls E),
                                        (nb095AlphaDummy589 x u D R S_cls f E)),
                                      ((nb095AlphaDummy588 D R S_cls E),
                                        (nb095AlphaDummy590 x u D R S_cls f E)),
                                      ((nb095AlphaDummy580 D R S_cls E),
                                        (nb095AlphaDummy582 x u D R S_cls f E)),
                                      ((nb095AlphaDummy579 D R S_cls E),
                                        (nb095AlphaDummy581 x u D R S_cls f E)),
                                      ((nb095AlphaDummy585 D R S_cls E),
                                        (nb095AlphaDummy586 x u D R S_cls f E)),
                                      ((nb095AlphaDummy583 D R S_cls E),
                                        (nb095AlphaDummy584 x u D R S_cls f E)),
                                      ((nb095AlphaDummy004 D R S_cls E),
                                        (nb095AlphaDummy006 x u D R S_cls f E)),
                                      ((nb095AlphaDummy003 D R S_cls E),
                                        (nb095AlphaDummy005 x u D R S_cls f E)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0084`. -/
@[expose]
noncomputable def nb095SplitAlpha0084 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy580 D R S_cls E), (nb095AlphaDummy582 x u D R S_cls f E)),
        ((nb095AlphaDummy579 D R S_cls E), (nb095AlphaDummy581 x u D R S_cls f E)),
        ((nb095AlphaDummy609 D R S_cls E), (nb095AlphaDummy610 x u D R S_cls f E)),
        ((nb095AlphaDummy583 D R S_cls E), (nb095AlphaDummy584 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy580 D R S_cls E))
          (Class.cv (nb095AlphaDummy004 D R S_cls E))) (Wff.neg
          (Wff.classEq (Class.cv (nb095AlphaDummy579 D R S_cls E))
            (synCun (synCphi (Class.cv (nb095AlphaDummy580 D R S_cls E)))
              (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy582 x u D R S_cls f E))
          (Class.cv (nb095AlphaDummy006 x u D R S_cls f E))) (Wff.neg
          (Wff.classEq (Class.cv (nb095AlphaDummy581 x u D R S_cls f E))
            (synCun (synCphi (Class.cv (nb095AlphaDummy582 x u D R S_cls f E)))
              (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there
          (show (nb095AlphaDummy004 D R S_cls E) ≠ (nb095AlphaDummy580 D R S_cls E) from
            (by
              unfold nb095AlphaDummy580;
              with_reducible
                exact
                  (Nat.ne_of_lt
                    (mem_lt_freshVar (nb095_support_mem_0630 D R S_cls E) 1)))) (show
            (nb095AlphaDummy006 x u D R S_cls f E) ≠
              (nb095AlphaDummy582 x u D R S_cls f E) from (by
              unfold nb095AlphaDummy582;
              with_reducible
                exact
                  (Nat.ne_of_lt
                    (mem_lt_freshVar (nb095_support_mem_0632 x u D R S_cls f E) 1))))
          (TAlphaVar.there (show
              (nb095AlphaDummy004 D R S_cls E) ≠ (nb095AlphaDummy579 D R S_cls E) from (by
                unfold nb095AlphaDummy579;
                with_reducible
                  exact
                    (Nat.ne_of_lt
                      (mem_lt_freshVar (nb095_support_mem_0630 D R S_cls E) 0)))) (show
              (nb095AlphaDummy006 x u D R S_cls f E) ≠
                (nb095AlphaDummy581 x u D R S_cls f E) from (by
                unfold nb095AlphaDummy581;
                with_reducible
                  exact
                    (Nat.ne_of_lt
                      (mem_lt_freshVar (nb095_support_mem_0632 x u D R S_cls f E) 0))))
            (TAlphaVar.there (show
                (nb095AlphaDummy004 D R S_cls E) ≠ (nb095AlphaDummy609 D R S_cls E) from
                (by
                  unfold nb095AlphaDummy609;
                  with_reducible
                    exact
                      (Nat.ne_of_lt
                        (mem_lt_freshVar (nb095_support_mem_0634 D R S_cls E) 0)))) (show
                (nb095AlphaDummy006 x u D R S_cls f E) ≠
                  (nb095AlphaDummy610 x u D R S_cls f E) from (by
                  unfold nb095AlphaDummy610;
                  with_reducible
                    exact
                      (Nat.ne_of_lt
                        (mem_lt_freshVar (nb095_support_mem_0635 x u D R S_cls f E) 0))))
              (TAlphaVar.there (show (nb095AlphaDummy004 D R S_cls E) ≠
                    (nb095AlphaDummy583 D R S_cls E) from (by
                    unfold nb095AlphaDummy583;
                    with_reducible
                      exact
                        (Nat.ne_of_lt
                          (mem_lt_freshVar (nb095_support_mem_0631 D R S_cls E) 0)))) (show
                  (nb095AlphaDummy006 x u D R S_cls f E) ≠
                    (nb095AlphaDummy584 x u D R S_cls f E) from (by
                    unfold nb095AlphaDummy584;
                    with_reducible
                      exact
                        (Nat.ne_of_lt
                          (mem_lt_freshVar (nb095_support_mem_0633 x u D R S_cls f E)
                            0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb095AlphaDummy003 D R S_cls E))).fv ∪
                ((Class.cv (nb095AlphaDummy004 D R S_cls E))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb095AlphaDummy005 x u D R S_cls f E))).fv ∪
                ((Class.cv (nb095AlphaDummy006 x u D R S_cls f E))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy580 D R S_cls E) ≠
                                        (nb095AlphaDummy587 D R S_cls E) from (by
                                        unfold nb095AlphaDummy587;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0608 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy582 x u D R S_cls f E) ≠
                                        (nb095AlphaDummy589 x u D R S_cls f E) from (by
                                        unfold nb095AlphaDummy589;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0609 x u D R S_cls f E)
                                                0)))) (TAlphaVar.there (show
                                        (nb095AlphaDummy580 D R S_cls E) ≠
        (nb095AlphaDummy588 D R S_cls E) from (by
                                          unfold nb095AlphaDummy588;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0608 D R S_cls E)
                                                  1)))) (show
                                        (nb095AlphaDummy582 x u D R S_cls f E) ≠
        (nb095AlphaDummy590 x u D R S_cls f E) from (by
                                          unfold nb095AlphaDummy590;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0609 x u D R S_cls f
                                                    E)
                                                  1)))) (TAlphaVar.there (show
        (nb095AlphaDummy580 D R S_cls E) ≠ (nb095AlphaDummy613 D R S_cls E) from (by
          unfold nb095AlphaDummy613;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0638 D R S_cls E)
                  0)))) (show (nb095AlphaDummy582 x u D R S_cls f E) ≠
        (nb095AlphaDummy614 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy614;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0639 x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy580 D R S_cls E) ≠
        (nb095AlphaDummy611 D R S_cls E) from (by
          unfold nb095AlphaDummy611;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0636 D R S_cls E)
                  0)))) (show (nb095AlphaDummy582 x u D R S_cls f E) ≠
        (nb095AlphaDummy612 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy612;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0637 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                  (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy580 D R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy582 x u D R S_cls f E))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy587 D R S_cls E) ≠
        (nb095AlphaDummy594 D R S_cls E) from (by
          unfold nb095AlphaDummy594;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0612
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy589 x u D R S_cls f E) ≠
        (nb095AlphaDummy597 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy597;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0613
                    x u D R S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy587 D R S_cls E) ≠
        (nb095AlphaDummy593 D R S_cls E) from (by
          unfold nb095AlphaDummy593;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0612
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy589 x u D R S_cls f E) ≠
        (nb095AlphaDummy596 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy596;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0613
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy587 D R S_cls E) ≠
        (nb095AlphaDummy591 D R S_cls E) from (by
          unfold
            nb095AlphaDummy591;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0610
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy589 x u D R S_cls f E) ≠
        (nb095AlphaDummy592 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy592;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0611
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy595 D R S_cls E), (nb095AlphaDummy598 x u D R S_cls f E)),
        ((nb095AlphaDummy594 D R S_cls E), (nb095AlphaDummy597 x u D R S_cls f E)),
        ((nb095AlphaDummy593 D R S_cls E), (nb095AlphaDummy596 x u D R S_cls f E)),
        ((nb095AlphaDummy591 D R S_cls E), (nb095AlphaDummy592 x u D R S_cls f E)),
        ((nb095AlphaDummy587 D R S_cls E), (nb095AlphaDummy589 x u D R S_cls f E)),
        ((nb095AlphaDummy588 D R S_cls E), (nb095AlphaDummy590 x u D R S_cls f E)),
        ((nb095AlphaDummy613 D R S_cls E), (nb095AlphaDummy614 x u D R S_cls f E)),
        ((nb095AlphaDummy611 D R S_cls E), (nb095AlphaDummy612 x u D R S_cls f E)),
        ((nb095AlphaDummy580 D R S_cls E), (nb095AlphaDummy582 x u D R S_cls f E)),
        ((nb095AlphaDummy579 D R S_cls E), (nb095AlphaDummy581 x u D R S_cls f E)),
        ((nb095AlphaDummy609 D R S_cls E), (nb095AlphaDummy610 x u D R S_cls f E)),
        ((nb095AlphaDummy583 D R S_cls E), (nb095AlphaDummy584 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy594 D R S_cls E) ≠
        (nb095AlphaDummy601 D R S_cls E) from (by
          unfold
            nb095AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0616
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy597 x u D R S_cls f E) ≠ (nb095AlphaDummy602
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy602;
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
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy594 D R S_cls E) ≠
        (nb095AlphaDummy599 D R S_cls E) from (by
          unfold
            nb095AlphaDummy599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0614
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy597 x u D R S_cls f E) ≠ (nb095AlphaDummy600
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy600;
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
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy587
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy589 x u D R S_cls f
        E))).fv ∪ ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy595
        D R S_cls E) ≠ (nb095AlphaDummy601 D R S_cls E) from (by
          unfold
            nb095AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0620
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy598 x u D R S_cls f E) ≠ (nb095AlphaDummy602
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy602;
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
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy595 D R S_cls E) ≠
        (nb095AlphaDummy599 D R S_cls E) from (by
          unfold
            nb095AlphaDummy599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0618
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy598 x u D R S_cls f E) ≠ (nb095AlphaDummy600
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy600;
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
        (TAlphaVar.there (show (nb095AlphaDummy594 D R S_cls E) ≠ (nb095AlphaDummy601 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0616
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy597 x u D R S_cls f E) ≠ (nb095AlphaDummy602
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy602;
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
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy594 D R S_cls E) ≠
        (nb095AlphaDummy599 D R S_cls E) from (by
          unfold
            nb095AlphaDummy599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0614
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy597 x u D R S_cls f E) ≠ (nb095AlphaDummy600
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy600;
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
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy587
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy589 x u D R S_cls f
        E))).fv ∪ ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy595
        D R S_cls E) ≠ (nb095AlphaDummy601 D R S_cls E) from (by
          unfold
            nb095AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0620
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy598 x u D R S_cls f E) ≠ (nb095AlphaDummy602
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy602;
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
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy595 D R S_cls E) ≠
        (nb095AlphaDummy599 D R S_cls E) from (by
          unfold
            nb095AlphaDummy599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0618
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy598 x u D R S_cls f E) ≠ (nb095AlphaDummy600
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy600;
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
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy595 D R S_cls E), (nb095AlphaDummy598 x u D R S_cls f E)),
        ((nb095AlphaDummy594 D R S_cls E), (nb095AlphaDummy597 x u D R S_cls f E)),
        ((nb095AlphaDummy593 D R S_cls E), (nb095AlphaDummy596 x u D R S_cls f E)),
        ((nb095AlphaDummy591 D R S_cls E), (nb095AlphaDummy592 x u D R S_cls f E)),
        ((nb095AlphaDummy587 D R S_cls E), (nb095AlphaDummy589 x u D R S_cls f E)),
        ((nb095AlphaDummy588 D R S_cls E), (nb095AlphaDummy590 x u D R S_cls f E)),
        ((nb095AlphaDummy613 D R S_cls E), (nb095AlphaDummy614 x u D R S_cls f E)),
        ((nb095AlphaDummy611 D R S_cls E), (nb095AlphaDummy612 x u D R S_cls f E)),
        ((nb095AlphaDummy580 D R S_cls E), (nb095AlphaDummy582 x u D R S_cls f E)),
        ((nb095AlphaDummy579 D R S_cls E), (nb095AlphaDummy581 x u D R S_cls f E)),
        ((nb095AlphaDummy609 D R S_cls E), (nb095AlphaDummy610 x u D R S_cls f E)),
        ((nb095AlphaDummy583 D R S_cls E), (nb095AlphaDummy584 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy587 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy589 x u D R S_cls f E))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy587 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy589 x u D R S_cls f E))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy594
        D R S_cls E) ≠ (nb095AlphaDummy605 D R S_cls E) from (by
          unfold
            nb095AlphaDummy605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0624
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy597 x u D R S_cls f E) ≠ (nb095AlphaDummy606
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy606;
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
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy594 D R S_cls E) ≠
        (nb095AlphaDummy603 D R S_cls E) from (by
          unfold
            nb095AlphaDummy603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0622
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy597 x u D R S_cls f E) ≠ (nb095AlphaDummy604
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy604;
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
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy587
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy589 x u D R S_cls f
        E))).fv ∪ ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy594
        D R S_cls E) ≠ (nb095AlphaDummy605 D R S_cls E) from (by
          unfold
            nb095AlphaDummy605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0624
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy597 x u D R S_cls f E) ≠ (nb095AlphaDummy606
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy606;
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
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy594 D R S_cls E) ≠
        (nb095AlphaDummy603 D R S_cls E) from (by
          unfold
            nb095AlphaDummy603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0622
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy597 x u D R S_cls f E) ≠ (nb095AlphaDummy604
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy604;
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
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy587
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy589 x u D R S_cls f
        E))).fv ∪ ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy595 D R S_cls E) ≠ (nb095AlphaDummy607 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy607;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0628
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy598 x u D R S_cls f E) ≠ (nb095AlphaDummy608
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy608;
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
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy595 D R S_cls E) ≠
        (nb095AlphaDummy603 D R S_cls E) from (by
          unfold
            nb095AlphaDummy603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0626
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy598 x u D R S_cls f E) ≠ (nb095AlphaDummy604
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy604;
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy595
        D R S_cls E) ≠ (nb095AlphaDummy607 D R S_cls E) from (by
          unfold
            nb095AlphaDummy607;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0628
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy598 x u D R S_cls f E) ≠ (nb095AlphaDummy608
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy608;
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
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy595 D R S_cls E) ≠
        (nb095AlphaDummy603 D R S_cls E) from (by
          unfold
            nb095AlphaDummy603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0626
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy598 x u D R S_cls f E) ≠ (nb095AlphaDummy604
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy604;
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
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy587 D R S_cls E) ≠
        (nb095AlphaDummy591 D R S_cls E) from (by
          unfold nb095AlphaDummy591;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0610 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy589 x u D R S_cls f E) ≠
        (nb095AlphaDummy592 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy592;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0611 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy591 D R S_cls E), (nb095AlphaDummy592 x u D R S_cls f E)),
        ((nb095AlphaDummy587 D R S_cls E), (nb095AlphaDummy589 x u D R S_cls f E)),
        ((nb095AlphaDummy588 D R S_cls E), (nb095AlphaDummy590 x u D R S_cls f E)),
        ((nb095AlphaDummy613 D R S_cls E), (nb095AlphaDummy614 x u D R S_cls f E)),
        ((nb095AlphaDummy611 D R S_cls E), (nb095AlphaDummy612 x u D R S_cls f E)),
        ((nb095AlphaDummy580 D R S_cls E), (nb095AlphaDummy582 x u D R S_cls f E)),
        ((nb095AlphaDummy579 D R S_cls E), (nb095AlphaDummy581 x u D R S_cls f E)),
        ((nb095AlphaDummy609 D R S_cls E), (nb095AlphaDummy610 x u D R S_cls f E)),
        ((nb095AlphaDummy583 D R S_cls E), (nb095AlphaDummy584 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy587 D R S_cls E) ≠
        (nb095AlphaDummy591 D R S_cls E) from (by
          unfold nb095AlphaDummy591;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0610 D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy589 x u D R S_cls f E) ≠
        (nb095AlphaDummy592 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy592;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0611 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy587 D R S_cls E) ≠
        (nb095AlphaDummy591 D R S_cls E) from (by
          unfold nb095AlphaDummy591;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0610 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy589 x u D R S_cls f E) ≠
        (nb095AlphaDummy592 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy592;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0611 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy591 D R S_cls E), (nb095AlphaDummy592 x u D R S_cls f E)),
        ((nb095AlphaDummy587 D R S_cls E), (nb095AlphaDummy589 x u D R S_cls f E)),
        ((nb095AlphaDummy588 D R S_cls E), (nb095AlphaDummy590 x u D R S_cls f E)),
        ((nb095AlphaDummy613 D R S_cls E), (nb095AlphaDummy614 x u D R S_cls f E)),
        ((nb095AlphaDummy611 D R S_cls E), (nb095AlphaDummy612 x u D R S_cls f E)),
        ((nb095AlphaDummy580 D R S_cls E), (nb095AlphaDummy582 x u D R S_cls f E)),
        ((nb095AlphaDummy579 D R S_cls E), (nb095AlphaDummy581 x u D R S_cls f E)),
        ((nb095AlphaDummy609 D R S_cls E), (nb095AlphaDummy610 x u D R S_cls f E)),
        ((nb095AlphaDummy583 D R S_cls E), (nb095AlphaDummy584 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCnnc)
        (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy580 D R S_cls E) ≠
                                        (nb095AlphaDummy587 D R S_cls E) from (by
                                        unfold nb095AlphaDummy587;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0608 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy582 x u D R S_cls f E) ≠
                                        (nb095AlphaDummy589 x u D R S_cls f E) from (by
                                        unfold nb095AlphaDummy589;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0609 x u D R S_cls f E)
                                                0)))) (TAlphaVar.there (show
                                        (nb095AlphaDummy580 D R S_cls E) ≠
        (nb095AlphaDummy588 D R S_cls E) from (by
                                          unfold nb095AlphaDummy588;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0608 D R S_cls E)
                                                  1)))) (show
                                        (nb095AlphaDummy582 x u D R S_cls f E) ≠
        (nb095AlphaDummy590 x u D R S_cls f E) from (by
                                          unfold nb095AlphaDummy590;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0609 x u D R S_cls f
                                                    E)
                                                  1)))) (TAlphaVar.there (show
        (nb095AlphaDummy580 D R S_cls E) ≠ (nb095AlphaDummy613 D R S_cls E) from (by
          unfold nb095AlphaDummy613;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0638 D R S_cls E)
                  0)))) (show (nb095AlphaDummy582 x u D R S_cls f E) ≠
        (nb095AlphaDummy614 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy614;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0639 x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy580 D R S_cls E) ≠
        (nb095AlphaDummy611 D R S_cls E) from (by
          unfold nb095AlphaDummy611;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0636 D R S_cls E)
                  0)))) (show (nb095AlphaDummy582 x u D R S_cls f E) ≠
        (nb095AlphaDummy612 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy612;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0637 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                  (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy580 D R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy582 x u D R S_cls f E))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy587 D R S_cls E) ≠
        (nb095AlphaDummy594 D R S_cls E) from (by
          unfold nb095AlphaDummy594;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0612
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy589 x u D R S_cls f E) ≠
        (nb095AlphaDummy597 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy597;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0613
                    x u D R S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy587 D R S_cls E) ≠
        (nb095AlphaDummy593 D R S_cls E) from (by
          unfold nb095AlphaDummy593;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0612
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy589 x u D R S_cls f E) ≠
        (nb095AlphaDummy596 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy596;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0613
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy587 D R S_cls E) ≠
        (nb095AlphaDummy591 D R S_cls E) from (by
          unfold
            nb095AlphaDummy591;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0610
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy589 x u D R S_cls f E) ≠
        (nb095AlphaDummy592 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy592;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0611
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy595 D R S_cls E), (nb095AlphaDummy598 x u D R S_cls f E)),
        ((nb095AlphaDummy594 D R S_cls E), (nb095AlphaDummy597 x u D R S_cls f E)),
        ((nb095AlphaDummy593 D R S_cls E), (nb095AlphaDummy596 x u D R S_cls f E)),
        ((nb095AlphaDummy591 D R S_cls E), (nb095AlphaDummy592 x u D R S_cls f E)),
        ((nb095AlphaDummy587 D R S_cls E), (nb095AlphaDummy589 x u D R S_cls f E)),
        ((nb095AlphaDummy588 D R S_cls E), (nb095AlphaDummy590 x u D R S_cls f E)),
        ((nb095AlphaDummy613 D R S_cls E), (nb095AlphaDummy614 x u D R S_cls f E)),
        ((nb095AlphaDummy611 D R S_cls E), (nb095AlphaDummy612 x u D R S_cls f E)),
        ((nb095AlphaDummy580 D R S_cls E), (nb095AlphaDummy582 x u D R S_cls f E)),
        ((nb095AlphaDummy579 D R S_cls E), (nb095AlphaDummy581 x u D R S_cls f E)),
        ((nb095AlphaDummy609 D R S_cls E), (nb095AlphaDummy610 x u D R S_cls f E)),
        ((nb095AlphaDummy583 D R S_cls E), (nb095AlphaDummy584 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy594 D R S_cls E) ≠
        (nb095AlphaDummy601 D R S_cls E) from (by
          unfold
            nb095AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0616
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy597 x u D R S_cls f E) ≠ (nb095AlphaDummy602
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy602;
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
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy594 D R S_cls E) ≠
        (nb095AlphaDummy599 D R S_cls E) from (by
          unfold
            nb095AlphaDummy599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0614
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy597 x u D R S_cls f E) ≠ (nb095AlphaDummy600
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy600;
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
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy587
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy589 x u D R S_cls f
        E))).fv ∪ ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy595
        D R S_cls E) ≠ (nb095AlphaDummy601 D R S_cls E) from (by
          unfold
            nb095AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0620
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy598 x u D R S_cls f E) ≠ (nb095AlphaDummy602
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy602;
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
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy595 D R S_cls E) ≠
        (nb095AlphaDummy599 D R S_cls E) from (by
          unfold
            nb095AlphaDummy599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0618
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy598 x u D R S_cls f E) ≠ (nb095AlphaDummy600
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy600;
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
        (TAlphaVar.there (show (nb095AlphaDummy594 D R S_cls E) ≠ (nb095AlphaDummy601 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0616
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy597 x u D R S_cls f E) ≠ (nb095AlphaDummy602
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy602;
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
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy594 D R S_cls E) ≠
        (nb095AlphaDummy599 D R S_cls E) from (by
          unfold
            nb095AlphaDummy599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0614
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy597 x u D R S_cls f E) ≠ (nb095AlphaDummy600
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy600;
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
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy587
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy589 x u D R S_cls f
        E))).fv ∪ ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy595
        D R S_cls E) ≠ (nb095AlphaDummy601 D R S_cls E) from (by
          unfold
            nb095AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0620
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy598 x u D R S_cls f E) ≠ (nb095AlphaDummy602
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy602;
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
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy595 D R S_cls E) ≠
        (nb095AlphaDummy599 D R S_cls E) from (by
          unfold
            nb095AlphaDummy599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0618
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy598 x u D R S_cls f E) ≠ (nb095AlphaDummy600
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy600;
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
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy595 D R S_cls E), (nb095AlphaDummy598 x u D R S_cls f E)),
        ((nb095AlphaDummy594 D R S_cls E), (nb095AlphaDummy597 x u D R S_cls f E)),
        ((nb095AlphaDummy593 D R S_cls E), (nb095AlphaDummy596 x u D R S_cls f E)),
        ((nb095AlphaDummy591 D R S_cls E), (nb095AlphaDummy592 x u D R S_cls f E)),
        ((nb095AlphaDummy587 D R S_cls E), (nb095AlphaDummy589 x u D R S_cls f E)),
        ((nb095AlphaDummy588 D R S_cls E), (nb095AlphaDummy590 x u D R S_cls f E)),
        ((nb095AlphaDummy613 D R S_cls E), (nb095AlphaDummy614 x u D R S_cls f E)),
        ((nb095AlphaDummy611 D R S_cls E), (nb095AlphaDummy612 x u D R S_cls f E)),
        ((nb095AlphaDummy580 D R S_cls E), (nb095AlphaDummy582 x u D R S_cls f E)),
        ((nb095AlphaDummy579 D R S_cls E), (nb095AlphaDummy581 x u D R S_cls f E)),
        ((nb095AlphaDummy609 D R S_cls E), (nb095AlphaDummy610 x u D R S_cls f E)),
        ((nb095AlphaDummy583 D R S_cls E), (nb095AlphaDummy584 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy587 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy589 x u D R S_cls f E))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy587 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy589 x u D R S_cls f E))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy594
        D R S_cls E) ≠ (nb095AlphaDummy605 D R S_cls E) from (by
          unfold
            nb095AlphaDummy605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0624
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy597 x u D R S_cls f E) ≠ (nb095AlphaDummy606
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy606;
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
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy594 D R S_cls E) ≠
        (nb095AlphaDummy603 D R S_cls E) from (by
          unfold
            nb095AlphaDummy603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0622
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy597 x u D R S_cls f E) ≠ (nb095AlphaDummy604
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy604;
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
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy587
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy589 x u D R S_cls f
        E))).fv ∪ ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy594
        D R S_cls E) ≠ (nb095AlphaDummy605 D R S_cls E) from (by
          unfold
            nb095AlphaDummy605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0624
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy597 x u D R S_cls f E) ≠ (nb095AlphaDummy606
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy606;
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
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy594 D R S_cls E) ≠
        (nb095AlphaDummy603 D R S_cls E) from (by
          unfold
            nb095AlphaDummy603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0622
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy597 x u D R S_cls f E) ≠ (nb095AlphaDummy604
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy604;
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
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy587
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy589 x u D R S_cls f
        E))).fv ∪ ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy595 D R S_cls E) ≠ (nb095AlphaDummy607 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy607;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0628
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy598 x u D R S_cls f E) ≠ (nb095AlphaDummy608
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy608;
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
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy595 D R S_cls E) ≠
        (nb095AlphaDummy603 D R S_cls E) from (by
          unfold
            nb095AlphaDummy603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0626
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy598 x u D R S_cls f E) ≠ (nb095AlphaDummy604
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy604;
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy595
        D R S_cls E) ≠ (nb095AlphaDummy607 D R S_cls E) from (by
          unfold
            nb095AlphaDummy607;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0628
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy598 x u D R S_cls f E) ≠ (nb095AlphaDummy608
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy608;
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
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy595 D R S_cls E) ≠
        (nb095AlphaDummy603 D R S_cls E) from (by
          unfold
            nb095AlphaDummy603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0626
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy598 x u D R S_cls f E) ≠ (nb095AlphaDummy604
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy604;
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
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy587 D R S_cls E) ≠
        (nb095AlphaDummy591 D R S_cls E) from (by
          unfold nb095AlphaDummy591;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0610 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy589 x u D R S_cls f E) ≠
        (nb095AlphaDummy592 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy592;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0611 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy591 D R S_cls E), (nb095AlphaDummy592 x u D R S_cls f E)),
        ((nb095AlphaDummy587 D R S_cls E), (nb095AlphaDummy589 x u D R S_cls f E)),
        ((nb095AlphaDummy588 D R S_cls E), (nb095AlphaDummy590 x u D R S_cls f E)),
        ((nb095AlphaDummy613 D R S_cls E), (nb095AlphaDummy614 x u D R S_cls f E)),
        ((nb095AlphaDummy611 D R S_cls E), (nb095AlphaDummy612 x u D R S_cls f E)),
        ((nb095AlphaDummy580 D R S_cls E), (nb095AlphaDummy582 x u D R S_cls f E)),
        ((nb095AlphaDummy579 D R S_cls E), (nb095AlphaDummy581 x u D R S_cls f E)),
        ((nb095AlphaDummy609 D R S_cls E), (nb095AlphaDummy610 x u D R S_cls f E)),
        ((nb095AlphaDummy583 D R S_cls E), (nb095AlphaDummy584 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy587 D R S_cls E) ≠
        (nb095AlphaDummy591 D R S_cls E) from (by
          unfold nb095AlphaDummy591;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0610 D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy589 x u D R S_cls f E) ≠
        (nb095AlphaDummy592 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy592;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0611 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy587 D R S_cls E) ≠
        (nb095AlphaDummy591 D R S_cls E) from (by
          unfold nb095AlphaDummy591;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0610 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy589 x u D R S_cls f E) ≠
        (nb095AlphaDummy592 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy592;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0611 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy591 D R S_cls E), (nb095AlphaDummy592 x u D R S_cls f E)),
        ((nb095AlphaDummy587 D R S_cls E), (nb095AlphaDummy589 x u D R S_cls f E)),
        ((nb095AlphaDummy588 D R S_cls E), (nb095AlphaDummy590 x u D R S_cls f E)),
        ((nb095AlphaDummy613 D R S_cls E), (nb095AlphaDummy614 x u D R S_cls f E)),
        ((nb095AlphaDummy611 D R S_cls E), (nb095AlphaDummy612 x u D R S_cls f E)),
        ((nb095AlphaDummy580 D R S_cls E), (nb095AlphaDummy582 x u D R S_cls f E)),
        ((nb095AlphaDummy579 D R S_cls E), (nb095AlphaDummy581 x u D R S_cls f E)),
        ((nb095AlphaDummy609 D R S_cls E), (nb095AlphaDummy610 x u D R S_cls f E)),
        ((nb095AlphaDummy583 D R S_cls E), (nb095AlphaDummy584 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed [((nb095AlphaDummy611 D R S_cls E),
                      (nb095AlphaDummy612 x u D R S_cls f E)),
                    ((nb095AlphaDummy580 D R S_cls E),
                      (nb095AlphaDummy582 x u D R S_cls f E)),
                    ((nb095AlphaDummy579 D R S_cls E),
                      (nb095AlphaDummy581 x u D R S_cls f E)),
                    ((nb095AlphaDummy609 D R S_cls E),
                      (nb095AlphaDummy610 x u D R S_cls f E)),
                    ((nb095AlphaDummy583 D R S_cls E),
                      (nb095AlphaDummy584 x u D R S_cls f E)),
                    ((nb095AlphaDummy004 D R S_cls E),
                      (nb095AlphaDummy006 x u D R S_cls f E)),
                    ((nb095AlphaDummy003 D R S_cls E),
                      (nb095AlphaDummy005 x u D R S_cls f E)),
                    ((nb095AlphaDummy001 D R S_cls E), u),
                    ((nb095AlphaDummy002 D R S_cls E), x),
                    ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

theorem nb095_focused_notmem_0052 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy617 D R S_cls E) ∉ R.fv :=
  by
  change
    freshVar
        ((R).fv ∪ ((synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))))).fv)
        0 ∉
      R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (hu))

theorem nb095_focused_notmem_0053 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy618 x D R) ∉ R.fv :=
  by
  change
    freshVar
        ((R).fv ∪ ((synCxp (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))))).fv)
        0 ∉
      R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (hu))

theorem nb095_focused_notmem_0054 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy615 D R S_cls E) ∉ R.fv :=
  by
  change
    freshVar
        (((synCnin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))))).fv ∪
          ((synCnin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin R
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synCin D
          (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0055 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy616 x D R) ∉ R.fv :=
  by
  change
    freshVar
        (((synCnin R (synCxp (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (Class.cv x))))))).fv ∪ ((synCnin R (synCxp (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (Class.cv x))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin R
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_compact_envfresh_0290 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_R_f : f ∉ R.fv) (dv_R_u : u ∉ R.fv)
    (dv_R_x : x ∉ R.fv) :
    TEnvFresh
      [((nb095AlphaDummy617 D R S_cls E), (nb095AlphaDummy618 x D R)),
        ((nb095AlphaDummy615 D R S_cls E), (nb095AlphaDummy616 x D R)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      R.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb095AlphaDummy617 D R S_cls E) (nb095AlphaDummy618 x D R)
      (nb095_focused_notmem_0052 D R S_cls E) (nb095_focused_notmem_0053 x D R)
      (TEnvFresh.consFresh (nb095AlphaDummy615 D R S_cls E)
        (nb095AlphaDummy616 x D R) (nb095_focused_notmem_0054 D R S_cls E)
        (nb095_focused_notmem_0055 x D R)
        (TEnvFresh.consFresh (nb095AlphaDummy004 D R S_cls E)
          (nb095AlphaDummy006 x u D R S_cls f E) (nb095_focused_notmem_0050 D R S_cls E)
          (nb095_focused_notmem_0051 x u D R S_cls f E)
          (TEnvFresh.consFresh (nb095AlphaDummy003 D R S_cls E)
            (nb095AlphaDummy005 x u D R S_cls f E) (nb095_focused_notmem_0046 D R S_cls E)
            (nb095_focused_notmem_0047 x u D R S_cls f E)
            (TEnvFresh.consFresh (nb095AlphaDummy001 D R S_cls E) u
              (nb095_focused_notmem_0018 D R S_cls E) dv_R_u
              (TEnvFresh.consFresh (nb095AlphaDummy002 D R S_cls E) x
                (nb095_focused_notmem_0019 D R S_cls E) dv_R_x
                (TEnvFresh.consFresh (nb095AlphaDummy000 D R S_cls E) f
                  (nb095_focused_notmem_0020 D R S_cls E) dv_R_f (TEnvFresh.nil R.fv))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
