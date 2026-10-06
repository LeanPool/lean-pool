/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C095M3Part042

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `AlphaSupport.NAR4H5C095M3Part043Stage1`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0095`. -/
@[expose]
noncomputable def nb095SplitAlpha0095 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_f_u : f ≠ u) (dv_f_x : f ≠ x) :
    TAlphaWff
      [((nb095AlphaDummy662 D R S_cls E), (nb095AlphaDummy664 x u D R S_cls f E)),
        ((nb095AlphaDummy661 D R S_cls E), (nb095AlphaDummy663 x u D R S_cls f E)),
        ((nb095AlphaDummy737 D R S_cls E), (nb095AlphaDummy738 x u D R S_cls f E)),
        ((nb095AlphaDummy665 D R S_cls E), (nb095AlphaDummy666 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy662 D R S_cls E))
          (synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
            (Class.cv (nb095AlphaDummy004 D R S_cls E)))) (Wff.neg
          (Wff.classEq (Class.cv (nb095AlphaDummy661 D R S_cls E))
            (synCun (synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E)))
              (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy664 x u D R S_cls f E))
          (synCfv (Class.cv f) (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)))) (Wff.neg
          (Wff.classEq (Class.cv (nb095AlphaDummy663 x u D R S_cls f E))
            (synCun (synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E)))
              (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there (freshVar_injective
                  (((Class.cab (nb095AlphaDummy741 D R S_cls E) (Wff.classEq
                        (Class.cab (nb095AlphaDummy739 D R S_cls E)
                          (synWbr (Class.cv (nb095AlphaDummy004 D R S_cls E))
                            (Class.cv (nb095AlphaDummy000 D R S_cls E))
                            (Class.cv (nb095AlphaDummy739 D R S_cls E))))
                        (synCsn (Class.cv (nb095AlphaDummy741 D R S_cls E)))))).fv)
                  (by decide)) (freshVar_injective
                  (((Class.cab (nb095AlphaDummy742 x u D R S_cls f E) (Wff.classEq
                        (Class.cab (nb095AlphaDummy740 x u D R S_cls f E)
                          (synWbr (Class.cv (nb095AlphaDummy006 x u D R S_cls f E))
                            (Class.cv f) (Class.cv (nb095AlphaDummy740 x u D R S_cls f E))))
                        (synCsn (Class.cv (nb095AlphaDummy742 x u D R S_cls f E)))))).fv)
                  (by decide)) (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.classMem (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                    (nb095SplitAlpha0093 x u D R S_cls f E)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy739 D R S_cls E) ≠
        (nb095AlphaDummy748 D R S_cls E) from (by
          unfold nb095AlphaDummy748;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0818 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy740 x u D R S_cls f E) ≠
        (nb095AlphaDummy750 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy750;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0820 x u
                    D R S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy739 D R S_cls E) ≠
        (nb095AlphaDummy747 D R S_cls E) from (by
          unfold nb095AlphaDummy747;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0818 D
                    R S_cls E)
                  0)))) (show (nb095AlphaDummy740 x u D R S_cls f E) ≠
        (nb095AlphaDummy749 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy749;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0820 x
                    u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy739 D R S_cls E) ≠
        (nb095AlphaDummy777 D R S_cls E) from (by
          unfold nb095AlphaDummy777;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0822
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy740 x u D R S_cls f E) ≠
        (nb095AlphaDummy778 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy778;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0823
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy739 D R S_cls E) ≠
        (nb095AlphaDummy751 D R S_cls E) from (by
          unfold nb095AlphaDummy751;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0819
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy740 x u D R S_cls f E) ≠
        (nb095AlphaDummy752 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy752;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0821
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy004 D R S_cls
        E))).fv ∪ ((Class.cv (nb095AlphaDummy739 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy006 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy740 x u D R S_cls f E))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0094 x u D R S_cls f E)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy779 D R S_cls E), (nb095AlphaDummy780 x u D R S_cls f E)),
        ((nb095AlphaDummy748 D R S_cls E), (nb095AlphaDummy750 x u D R S_cls f E)),
        ((nb095AlphaDummy747 D R S_cls E), (nb095AlphaDummy749 x u D R S_cls f E)),
        ((nb095AlphaDummy777 D R S_cls E), (nb095AlphaDummy778 x u D R S_cls f E)),
        ((nb095AlphaDummy751 D R S_cls E), (nb095AlphaDummy752 x u D R S_cls f E)),
        ((nb095AlphaDummy739 D R S_cls E), (nb095AlphaDummy740 x u D R S_cls f E)),
        ((nb095AlphaDummy741 D R S_cls E), (nb095AlphaDummy742 x u D R S_cls f E)),
        ((nb095AlphaDummy744 D R S_cls E), (nb095AlphaDummy746 x u D R S_cls f E)),
        ((nb095AlphaDummy743 D R S_cls E), (nb095AlphaDummy745 x u D R S_cls f E)),
        ((nb095AlphaDummy662 D R S_cls E), (nb095AlphaDummy664 x u D R S_cls f E)),
        ((nb095AlphaDummy661 D R S_cls E), (nb095AlphaDummy663 x u D R S_cls f E)),
        ((nb095AlphaDummy737 D R S_cls E), (nb095AlphaDummy738 x u D R S_cls f E)),
        ((nb095AlphaDummy665 D R S_cls E), (nb095AlphaDummy666 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy739 D R S_cls E) ≠
        (nb095AlphaDummy748 D R S_cls E) from (by
          unfold nb095AlphaDummy748;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0818 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy740 x u D R S_cls f E) ≠
        (nb095AlphaDummy750 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy750;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0820 x u
                    D R S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy739 D R S_cls E) ≠
        (nb095AlphaDummy747 D R S_cls E) from (by
          unfold nb095AlphaDummy747;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0818 D
                    R S_cls E)
                  0)))) (show (nb095AlphaDummy740 x u D R S_cls f E) ≠
        (nb095AlphaDummy749 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy749;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0820 x
                    u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy739 D R S_cls E) ≠
        (nb095AlphaDummy777 D R S_cls E) from (by
          unfold nb095AlphaDummy777;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0822
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy740 x u D R S_cls f E) ≠
        (nb095AlphaDummy778 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy778;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0823
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy739 D R S_cls E) ≠
        (nb095AlphaDummy751 D R S_cls E) from (by
          unfold nb095AlphaDummy751;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0819
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy740 x u D R S_cls f E) ≠
        (nb095AlphaDummy752 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy752;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0821
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy004 D R S_cls
        E))).fv ∪ ((Class.cv (nb095AlphaDummy739 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy006 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy740 x u D R S_cls f E))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0094 x u D R S_cls f E)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy779 D R S_cls E), (nb095AlphaDummy780 x u D R S_cls f E)),
        ((nb095AlphaDummy748 D R S_cls E), (nb095AlphaDummy750 x u D R S_cls f E)),
        ((nb095AlphaDummy747 D R S_cls E), (nb095AlphaDummy749 x u D R S_cls f E)),
        ((nb095AlphaDummy777 D R S_cls E), (nb095AlphaDummy778 x u D R S_cls f E)),
        ((nb095AlphaDummy751 D R S_cls E), (nb095AlphaDummy752 x u D R S_cls f E)),
        ((nb095AlphaDummy739 D R S_cls E), (nb095AlphaDummy740 x u D R S_cls f E)),
        ((nb095AlphaDummy741 D R S_cls E), (nb095AlphaDummy742 x u D R S_cls f E)),
        ((nb095AlphaDummy744 D R S_cls E), (nb095AlphaDummy746 x u D R S_cls f E)),
        ((nb095AlphaDummy743 D R S_cls E), (nb095AlphaDummy745 x u D R S_cls f E)),
        ((nb095AlphaDummy662 D R S_cls E), (nb095AlphaDummy664 x u D R S_cls f E)),
        ((nb095AlphaDummy661 D R S_cls E), (nb095AlphaDummy663 x u D R S_cls f E)),
        ((nb095AlphaDummy737 D R S_cls E), (nb095AlphaDummy738 x u D R S_cls f E)),
        ((nb095AlphaDummy665 D R S_cls E), (nb095AlphaDummy666 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
                            (nb095AlphaDummy000 D R S_cls E) ≠
                              (nb095AlphaDummy739 D R S_cls E) from (by
                              unfold nb095AlphaDummy739;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0830 D R S_cls E)
                                      0))))
                          (show f ≠ (nb095AlphaDummy740 x u D R S_cls f E) from (by
                              unfold nb095AlphaDummy740;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb095_support_mem_0833 x u D R S_cls f E) 0))))
                          (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
                                (nb095AlphaDummy741 D R S_cls E) from (by
                                unfold nb095AlphaDummy741;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0831 D R S_cls E) 0))))
                            (show f ≠ (nb095AlphaDummy742 x u D R S_cls f E) from (by
                                unfold nb095AlphaDummy742;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0834 x u D R S_cls f E) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
                                  (nb095AlphaDummy744 D R S_cls E) from (by
                                  unfold nb095AlphaDummy744;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0832 D R S_cls E) 1))))
                              (show f ≠ (nb095AlphaDummy746 x u D R S_cls f E) from (by
                                  unfold nb095AlphaDummy746;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0835 x u D R S_cls f E) 1))))
                              (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
                                    (nb095AlphaDummy743 D R S_cls E) from (by
                                    unfold nb095AlphaDummy743;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0832 D R S_cls E) 0))))
                                (show f ≠ (nb095AlphaDummy745 x u D R S_cls f E) from (by
                                    unfold nb095AlphaDummy745;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0835 x u D R S_cls f E)
                                            0)))) (TAlphaVar.there (show
                                    (nb095AlphaDummy000 D R S_cls E) ≠
                                      (nb095AlphaDummy662 D R S_cls E) from (by
                                      unfold nb095AlphaDummy662;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0742 D R S_cls E) 1))))
                                  (show f ≠ (nb095AlphaDummy664 x u D R S_cls f E) from (by
                                      unfold nb095AlphaDummy664;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0744 x u D R S_cls f E)
                                              1)))) (TAlphaVar.there (show
                                      (nb095AlphaDummy000 D R S_cls E) ≠
                                        (nb095AlphaDummy661 D R S_cls E) from (by
                                        unfold nb095AlphaDummy661;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0742 D R S_cls E) 0))))
                                    (show f ≠ (nb095AlphaDummy663 x u D R S_cls f E) from (by
                                        unfold nb095AlphaDummy663;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0744 x u D R S_cls f E)
                                                0)))) (TAlphaVar.there (show
                                        (nb095AlphaDummy000 D R S_cls E) ≠
        (nb095AlphaDummy737 D R S_cls E) from (by
                                          unfold nb095AlphaDummy737;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0828 D R S_cls E)
                                                  0))))
                                      (show f ≠ (nb095AlphaDummy738 x u D R S_cls f E) from
                                        (by
                                          unfold nb095AlphaDummy738;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0829 x u D R S_cls f
                                                    E)
                                                  0)))) (TAlphaVar.there (show
        (nb095AlphaDummy000 D R S_cls E) ≠ (nb095AlphaDummy665 D R S_cls E) from (by
          unfold nb095AlphaDummy665;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0743 D R S_cls E)
                  0)))) (show f ≠ (nb095AlphaDummy666 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy666;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0745 x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
        (nb095AlphaDummy004 D R S_cls E) from (by
          unfold nb095AlphaDummy004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0740 D R S_cls E)
                  1)))) (show f ≠ (nb095AlphaDummy006 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0741 x u D R
                    S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
        (nb095AlphaDummy003 D R S_cls E) from (by
          unfold nb095AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0740 D R S_cls
                    E)
                  0)))) (show f ≠ (nb095AlphaDummy005 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0741 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (freshVar_injective
        ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) (by decide)) dv_f_u (TAlphaVar.there
        (freshVar_injective ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) (by decide)) dv_f_x
        (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.cab
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095AlphaDummy741 D R S_cls E) ≠
                              (nb095AlphaDummy783 D R S_cls E) from (by
                              unfold nb095AlphaDummy783;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0836 D R S_cls E)
                                      0)))) (show (nb095AlphaDummy742 x u D R S_cls f E) ≠
                              (nb095AlphaDummy784 x u D R S_cls f E) from (by
                              unfold nb095AlphaDummy784;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb095_support_mem_0837 x u D R S_cls f E) 0))))
                          (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
                    (Class.cv (nb095AlphaDummy003 D R S_cls E)))).fv ∪
                ((synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
                    (Class.cv (nb095AlphaDummy004 D R S_cls E)))).fv) (by decide))
            (freshVar_injective (((synCfv (Class.cv f)
                    (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)))).fv ∪
                ((synCfv (Class.cv f)
                    (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy662 D R S_cls E) ≠
                                        (nb095AlphaDummy715 D R S_cls E) from (by
                                        unfold nb095AlphaDummy715;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0756 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy664 x u D R S_cls f E) ≠
                                        (nb095AlphaDummy717 x u D R S_cls f E) from (by
                                        unfold nb095AlphaDummy717;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0757 x u D R S_cls f E)
                                                0)))) (TAlphaVar.there (show
                                        (nb095AlphaDummy662 D R S_cls E) ≠
        (nb095AlphaDummy716 D R S_cls E) from (by
                                          unfold nb095AlphaDummy716;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0756 D R S_cls E)
                                                  1)))) (show
                                        (nb095AlphaDummy664 x u D R S_cls f E) ≠
        (nb095AlphaDummy718 x u D R S_cls f E) from (by
                                          unfold nb095AlphaDummy718;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0757 x u D R S_cls f
                                                    E)
                                                  1)))) (TAlphaVar.there (show
        (nb095AlphaDummy662 D R S_cls E) ≠ (nb095AlphaDummy787 D R S_cls E) from (by
          unfold nb095AlphaDummy787;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0840 D R S_cls E)
                  0)))) (show (nb095AlphaDummy664 x u D R S_cls f E) ≠
        (nb095AlphaDummy788 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy788;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0841 x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy662 D R S_cls E) ≠
        (nb095AlphaDummy785 D R S_cls E) from (by
          unfold nb095AlphaDummy785;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0838 D R S_cls E)
                  0)))) (show (nb095AlphaDummy664 x u D R S_cls f E) ≠
        (nb095AlphaDummy786 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy786;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0839 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                  (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy662 D R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy664 x u D R S_cls f E))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy715 D R S_cls E) ≠
        (nb095AlphaDummy722 D R S_cls E) from (by
          unfold nb095AlphaDummy722;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0760
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy717 x u D R S_cls f E) ≠
        (nb095AlphaDummy725 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy725;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0761
                    x u D R S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy715 D R S_cls E) ≠
        (nb095AlphaDummy721 D R S_cls E) from (by
          unfold nb095AlphaDummy721;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0760
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy717 x u D R S_cls f E) ≠
        (nb095AlphaDummy724 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy724;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0761
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy715 D R S_cls E) ≠
        (nb095AlphaDummy719 D R S_cls E) from (by
          unfold
            nb095AlphaDummy719;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0758
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy717 x u D R S_cls f E) ≠
        (nb095AlphaDummy720 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy720;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0759
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy723 D R S_cls E), (nb095AlphaDummy726 x u D R S_cls f E)),
        ((nb095AlphaDummy722 D R S_cls E), (nb095AlphaDummy725 x u D R S_cls f E)),
        ((nb095AlphaDummy721 D R S_cls E), (nb095AlphaDummy724 x u D R S_cls f E)),
        ((nb095AlphaDummy719 D R S_cls E), (nb095AlphaDummy720 x u D R S_cls f E)),
        ((nb095AlphaDummy715 D R S_cls E), (nb095AlphaDummy717 x u D R S_cls f E)),
        ((nb095AlphaDummy716 D R S_cls E), (nb095AlphaDummy718 x u D R S_cls f E)),
        ((nb095AlphaDummy787 D R S_cls E), (nb095AlphaDummy788 x u D R S_cls f E)),
        ((nb095AlphaDummy785 D R S_cls E), (nb095AlphaDummy786 x u D R S_cls f E)),
        ((nb095AlphaDummy662 D R S_cls E), (nb095AlphaDummy664 x u D R S_cls f E)),
        ((nb095AlphaDummy661 D R S_cls E), (nb095AlphaDummy663 x u D R S_cls f E)),
        ((nb095AlphaDummy737 D R S_cls E), (nb095AlphaDummy738 x u D R S_cls f E)),
        ((nb095AlphaDummy665 D R S_cls E), (nb095AlphaDummy666 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy722 D R S_cls E) ≠
        (nb095AlphaDummy729 D R S_cls E) from (by
          unfold
            nb095AlphaDummy729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0764
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy725 x u D R S_cls f E) ≠ (nb095AlphaDummy730
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy730;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0765
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy722 D R S_cls E) ≠
        (nb095AlphaDummy727 D R S_cls E) from (by
          unfold
            nb095AlphaDummy727;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0762
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy725 x u D R S_cls f E) ≠ (nb095AlphaDummy728
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy728;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0763
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy715
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy717 x u D R S_cls f
        E))).fv ∪ ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy723
        D R S_cls E) ≠ (nb095AlphaDummy729 D R S_cls E) from (by
          unfold
            nb095AlphaDummy729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0768
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy726 x u D R S_cls f E) ≠ (nb095AlphaDummy730
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy730;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0769
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy723 D R S_cls E) ≠
        (nb095AlphaDummy727 D R S_cls E) from (by
          unfold
            nb095AlphaDummy727;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0766
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy726 x u D R S_cls f E) ≠ (nb095AlphaDummy728
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy728;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0767
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
        (TAlphaVar.there (show (nb095AlphaDummy722 D R S_cls E) ≠ (nb095AlphaDummy729 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0764
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy725 x u D R S_cls f E) ≠ (nb095AlphaDummy730
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy730;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0765
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy722 D R S_cls E) ≠
        (nb095AlphaDummy727 D R S_cls E) from (by
          unfold
            nb095AlphaDummy727;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0762
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy725 x u D R S_cls f E) ≠ (nb095AlphaDummy728
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy728;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0763
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy715
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy717 x u D R S_cls f
        E))).fv ∪ ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy723
        D R S_cls E) ≠ (nb095AlphaDummy729 D R S_cls E) from (by
          unfold
            nb095AlphaDummy729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0768
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy726 x u D R S_cls f E) ≠ (nb095AlphaDummy730
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy730;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0769
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy723 D R S_cls E) ≠
        (nb095AlphaDummy727 D R S_cls E) from (by
          unfold
            nb095AlphaDummy727;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0766
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy726 x u D R S_cls f E) ≠ (nb095AlphaDummy728
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy728;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0767
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy723 D R S_cls E), (nb095AlphaDummy726 x u D R S_cls f E)),
        ((nb095AlphaDummy722 D R S_cls E), (nb095AlphaDummy725 x u D R S_cls f E)),
        ((nb095AlphaDummy721 D R S_cls E), (nb095AlphaDummy724 x u D R S_cls f E)),
        ((nb095AlphaDummy719 D R S_cls E), (nb095AlphaDummy720 x u D R S_cls f E)),
        ((nb095AlphaDummy715 D R S_cls E), (nb095AlphaDummy717 x u D R S_cls f E)),
        ((nb095AlphaDummy716 D R S_cls E), (nb095AlphaDummy718 x u D R S_cls f E)),
        ((nb095AlphaDummy787 D R S_cls E), (nb095AlphaDummy788 x u D R S_cls f E)),
        ((nb095AlphaDummy785 D R S_cls E), (nb095AlphaDummy786 x u D R S_cls f E)),
        ((nb095AlphaDummy662 D R S_cls E), (nb095AlphaDummy664 x u D R S_cls f E)),
        ((nb095AlphaDummy661 D R S_cls E), (nb095AlphaDummy663 x u D R S_cls f E)),
        ((nb095AlphaDummy737 D R S_cls E), (nb095AlphaDummy738 x u D R S_cls f E)),
        ((nb095AlphaDummy665 D R S_cls E), (nb095AlphaDummy666 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy715 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy717 x u D R S_cls f E))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy715 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy717 x u D R S_cls f E))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy722
        D R S_cls E) ≠ (nb095AlphaDummy733 D R S_cls E) from (by
          unfold
            nb095AlphaDummy733;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0772
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy725 x u D R S_cls f E) ≠ (nb095AlphaDummy734
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy734;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0773
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy722 D R S_cls E) ≠
        (nb095AlphaDummy731 D R S_cls E) from (by
          unfold
            nb095AlphaDummy731;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0770
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy725 x u D R S_cls f E) ≠ (nb095AlphaDummy732
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy732;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0771
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy715
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy717 x u D R S_cls f
        E))).fv ∪ ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy722
        D R S_cls E) ≠ (nb095AlphaDummy733 D R S_cls E) from (by
          unfold
            nb095AlphaDummy733;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0772
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy725 x u D R S_cls f E) ≠ (nb095AlphaDummy734
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy734;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0773
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy722 D R S_cls E) ≠
        (nb095AlphaDummy731 D R S_cls E) from (by
          unfold
            nb095AlphaDummy731;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0770
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy725 x u D R S_cls f E) ≠ (nb095AlphaDummy732
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy732;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0771
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy715
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy717 x u D R S_cls f
        E))).fv ∪ ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy723 D R S_cls E) ≠ (nb095AlphaDummy735 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0776
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy726 x u D R S_cls f E) ≠ (nb095AlphaDummy736
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0777
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy723 D R S_cls E) ≠
        (nb095AlphaDummy731 D R S_cls E) from (by
          unfold
            nb095AlphaDummy731;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0774
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy726 x u D R S_cls f E) ≠ (nb095AlphaDummy732
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy732;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0775
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy723
        D R S_cls E) ≠ (nb095AlphaDummy735 D R S_cls E) from (by
          unfold
            nb095AlphaDummy735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0776
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy726 x u D R S_cls f E) ≠ (nb095AlphaDummy736
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0777
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy723 D R S_cls E) ≠
        (nb095AlphaDummy731 D R S_cls E) from (by
          unfold
            nb095AlphaDummy731;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0774
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy726 x u D R S_cls f E) ≠ (nb095AlphaDummy732
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy732;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0775
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy715 D R S_cls E) ≠
        (nb095AlphaDummy719 D R S_cls E) from (by
          unfold nb095AlphaDummy719;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0758 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy717 x u D R S_cls f E) ≠
        (nb095AlphaDummy720 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy720;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0759 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy719 D R S_cls E), (nb095AlphaDummy720 x u D R S_cls f E)),
        ((nb095AlphaDummy715 D R S_cls E), (nb095AlphaDummy717 x u D R S_cls f E)),
        ((nb095AlphaDummy716 D R S_cls E), (nb095AlphaDummy718 x u D R S_cls f E)),
        ((nb095AlphaDummy787 D R S_cls E), (nb095AlphaDummy788 x u D R S_cls f E)),
        ((nb095AlphaDummy785 D R S_cls E), (nb095AlphaDummy786 x u D R S_cls f E)),
        ((nb095AlphaDummy662 D R S_cls E), (nb095AlphaDummy664 x u D R S_cls f E)),
        ((nb095AlphaDummy661 D R S_cls E), (nb095AlphaDummy663 x u D R S_cls f E)),
        ((nb095AlphaDummy737 D R S_cls E), (nb095AlphaDummy738 x u D R S_cls f E)),
        ((nb095AlphaDummy665 D R S_cls E), (nb095AlphaDummy666 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy715 D R S_cls E) ≠
        (nb095AlphaDummy719 D R S_cls E) from (by
          unfold nb095AlphaDummy719;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0758 D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy717 x u D R S_cls f E) ≠
        (nb095AlphaDummy720 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy720;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0759 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy715 D R S_cls E) ≠
        (nb095AlphaDummy719 D R S_cls E) from (by
          unfold nb095AlphaDummy719;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0758 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy717 x u D R S_cls f E) ≠
        (nb095AlphaDummy720 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy720;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0759 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy719 D R S_cls E), (nb095AlphaDummy720 x u D R S_cls f E)),
        ((nb095AlphaDummy715 D R S_cls E), (nb095AlphaDummy717 x u D R S_cls f E)),
        ((nb095AlphaDummy716 D R S_cls E), (nb095AlphaDummy718 x u D R S_cls f E)),
        ((nb095AlphaDummy787 D R S_cls E), (nb095AlphaDummy788 x u D R S_cls f E)),
        ((nb095AlphaDummy785 D R S_cls E), (nb095AlphaDummy786 x u D R S_cls f E)),
        ((nb095AlphaDummy662 D R S_cls E), (nb095AlphaDummy664 x u D R S_cls f E)),
        ((nb095AlphaDummy661 D R S_cls E), (nb095AlphaDummy663 x u D R S_cls f E)),
        ((nb095AlphaDummy737 D R S_cls E), (nb095AlphaDummy738 x u D R S_cls f E)),
        ((nb095AlphaDummy665 D R S_cls E), (nb095AlphaDummy666 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCnnc)
        (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy662 D R S_cls E) ≠
                                        (nb095AlphaDummy715 D R S_cls E) from (by
                                        unfold nb095AlphaDummy715;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0756 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy664 x u D R S_cls f E) ≠
                                        (nb095AlphaDummy717 x u D R S_cls f E) from (by
                                        unfold nb095AlphaDummy717;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0757 x u D R S_cls f E)
                                                0)))) (TAlphaVar.there (show
                                        (nb095AlphaDummy662 D R S_cls E) ≠
        (nb095AlphaDummy716 D R S_cls E) from (by
                                          unfold nb095AlphaDummy716;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0756 D R S_cls E)
                                                  1)))) (show
                                        (nb095AlphaDummy664 x u D R S_cls f E) ≠
        (nb095AlphaDummy718 x u D R S_cls f E) from (by
                                          unfold nb095AlphaDummy718;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0757 x u D R S_cls f
                                                    E)
                                                  1)))) (TAlphaVar.there (show
        (nb095AlphaDummy662 D R S_cls E) ≠ (nb095AlphaDummy787 D R S_cls E) from (by
          unfold nb095AlphaDummy787;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0840 D R S_cls E)
                  0)))) (show (nb095AlphaDummy664 x u D R S_cls f E) ≠
        (nb095AlphaDummy788 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy788;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0841 x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy662 D R S_cls E) ≠
        (nb095AlphaDummy785 D R S_cls E) from (by
          unfold nb095AlphaDummy785;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0838 D R S_cls E)
                  0)))) (show (nb095AlphaDummy664 x u D R S_cls f E) ≠
        (nb095AlphaDummy786 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy786;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0839 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                  (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy662 D R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy664 x u D R S_cls f E))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy715 D R S_cls E) ≠
        (nb095AlphaDummy722 D R S_cls E) from (by
          unfold nb095AlphaDummy722;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0760
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy717 x u D R S_cls f E) ≠
        (nb095AlphaDummy725 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy725;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0761
                    x u D R S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy715 D R S_cls E) ≠
        (nb095AlphaDummy721 D R S_cls E) from (by
          unfold nb095AlphaDummy721;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0760
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy717 x u D R S_cls f E) ≠
        (nb095AlphaDummy724 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy724;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0761
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy715 D R S_cls E) ≠
        (nb095AlphaDummy719 D R S_cls E) from (by
          unfold
            nb095AlphaDummy719;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0758
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy717 x u D R S_cls f E) ≠
        (nb095AlphaDummy720 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy720;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0759
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy723 D R S_cls E), (nb095AlphaDummy726 x u D R S_cls f E)),
        ((nb095AlphaDummy722 D R S_cls E), (nb095AlphaDummy725 x u D R S_cls f E)),
        ((nb095AlphaDummy721 D R S_cls E), (nb095AlphaDummy724 x u D R S_cls f E)),
        ((nb095AlphaDummy719 D R S_cls E), (nb095AlphaDummy720 x u D R S_cls f E)),
        ((nb095AlphaDummy715 D R S_cls E), (nb095AlphaDummy717 x u D R S_cls f E)),
        ((nb095AlphaDummy716 D R S_cls E), (nb095AlphaDummy718 x u D R S_cls f E)),
        ((nb095AlphaDummy787 D R S_cls E), (nb095AlphaDummy788 x u D R S_cls f E)),
        ((nb095AlphaDummy785 D R S_cls E), (nb095AlphaDummy786 x u D R S_cls f E)),
        ((nb095AlphaDummy662 D R S_cls E), (nb095AlphaDummy664 x u D R S_cls f E)),
        ((nb095AlphaDummy661 D R S_cls E), (nb095AlphaDummy663 x u D R S_cls f E)),
        ((nb095AlphaDummy737 D R S_cls E), (nb095AlphaDummy738 x u D R S_cls f E)),
        ((nb095AlphaDummy665 D R S_cls E), (nb095AlphaDummy666 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy722 D R S_cls E) ≠
        (nb095AlphaDummy729 D R S_cls E) from (by
          unfold
            nb095AlphaDummy729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0764
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy725 x u D R S_cls f E) ≠ (nb095AlphaDummy730
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy730;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0765
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy722 D R S_cls E) ≠
        (nb095AlphaDummy727 D R S_cls E) from (by
          unfold
            nb095AlphaDummy727;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0762
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy725 x u D R S_cls f E) ≠ (nb095AlphaDummy728
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy728;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0763
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy715
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy717 x u D R S_cls f
        E))).fv ∪ ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy723
        D R S_cls E) ≠ (nb095AlphaDummy729 D R S_cls E) from (by
          unfold
            nb095AlphaDummy729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0768
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy726 x u D R S_cls f E) ≠ (nb095AlphaDummy730
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy730;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0769
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy723 D R S_cls E) ≠
        (nb095AlphaDummy727 D R S_cls E) from (by
          unfold
            nb095AlphaDummy727;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0766
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy726 x u D R S_cls f E) ≠ (nb095AlphaDummy728
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy728;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0767
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
        (TAlphaVar.there (show (nb095AlphaDummy722 D R S_cls E) ≠ (nb095AlphaDummy729 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0764
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy725 x u D R S_cls f E) ≠ (nb095AlphaDummy730
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy730;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0765
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy722 D R S_cls E) ≠
        (nb095AlphaDummy727 D R S_cls E) from (by
          unfold
            nb095AlphaDummy727;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0762
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy725 x u D R S_cls f E) ≠ (nb095AlphaDummy728
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy728;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0763
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy715
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy717 x u D R S_cls f
        E))).fv ∪ ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy723
        D R S_cls E) ≠ (nb095AlphaDummy729 D R S_cls E) from (by
          unfold
            nb095AlphaDummy729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0768
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy726 x u D R S_cls f E) ≠ (nb095AlphaDummy730
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy730;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0769
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy723 D R S_cls E) ≠
        (nb095AlphaDummy727 D R S_cls E) from (by
          unfold
            nb095AlphaDummy727;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0766
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy726 x u D R S_cls f E) ≠ (nb095AlphaDummy728
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy728;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0767
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy723 D R S_cls E), (nb095AlphaDummy726 x u D R S_cls f E)),
        ((nb095AlphaDummy722 D R S_cls E), (nb095AlphaDummy725 x u D R S_cls f E)),
        ((nb095AlphaDummy721 D R S_cls E), (nb095AlphaDummy724 x u D R S_cls f E)),
        ((nb095AlphaDummy719 D R S_cls E), (nb095AlphaDummy720 x u D R S_cls f E)),
        ((nb095AlphaDummy715 D R S_cls E), (nb095AlphaDummy717 x u D R S_cls f E)),
        ((nb095AlphaDummy716 D R S_cls E), (nb095AlphaDummy718 x u D R S_cls f E)),
        ((nb095AlphaDummy787 D R S_cls E), (nb095AlphaDummy788 x u D R S_cls f E)),
        ((nb095AlphaDummy785 D R S_cls E), (nb095AlphaDummy786 x u D R S_cls f E)),
        ((nb095AlphaDummy662 D R S_cls E), (nb095AlphaDummy664 x u D R S_cls f E)),
        ((nb095AlphaDummy661 D R S_cls E), (nb095AlphaDummy663 x u D R S_cls f E)),
        ((nb095AlphaDummy737 D R S_cls E), (nb095AlphaDummy738 x u D R S_cls f E)),
        ((nb095AlphaDummy665 D R S_cls E), (nb095AlphaDummy666 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy715 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy717 x u D R S_cls f E))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy715 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy717 x u D R S_cls f E))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy722
        D R S_cls E) ≠ (nb095AlphaDummy733 D R S_cls E) from (by
          unfold
            nb095AlphaDummy733;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0772
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy725 x u D R S_cls f E) ≠ (nb095AlphaDummy734
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy734;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0773
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy722 D R S_cls E) ≠
        (nb095AlphaDummy731 D R S_cls E) from (by
          unfold
            nb095AlphaDummy731;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0770
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy725 x u D R S_cls f E) ≠ (nb095AlphaDummy732
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy732;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0771
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy715
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy717 x u D R S_cls f
        E))).fv ∪ ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy722
        D R S_cls E) ≠ (nb095AlphaDummy733 D R S_cls E) from (by
          unfold
            nb095AlphaDummy733;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0772
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy725 x u D R S_cls f E) ≠ (nb095AlphaDummy734
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy734;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0773
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy722 D R S_cls E) ≠
        (nb095AlphaDummy731 D R S_cls E) from (by
          unfold
            nb095AlphaDummy731;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0770
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy725 x u D R S_cls f E) ≠ (nb095AlphaDummy732
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy732;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0771
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy715
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy717 x u D R S_cls f
        E))).fv ∪ ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy723 D R S_cls E) ≠ (nb095AlphaDummy735 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0776
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy726 x u D R S_cls f E) ≠ (nb095AlphaDummy736
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0777
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy723 D R S_cls E) ≠
        (nb095AlphaDummy731 D R S_cls E) from (by
          unfold
            nb095AlphaDummy731;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0774
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy726 x u D R S_cls f E) ≠ (nb095AlphaDummy732
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy732;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0775
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy723
        D R S_cls E) ≠ (nb095AlphaDummy735 D R S_cls E) from (by
          unfold
            nb095AlphaDummy735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0776
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy726 x u D R S_cls f E) ≠ (nb095AlphaDummy736
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0777
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy723 D R S_cls E) ≠
        (nb095AlphaDummy731 D R S_cls E) from (by
          unfold
            nb095AlphaDummy731;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0774
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy726 x u D R S_cls f E) ≠ (nb095AlphaDummy732
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy732;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0775
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy715 D R S_cls E) ≠
        (nb095AlphaDummy719 D R S_cls E) from (by
          unfold nb095AlphaDummy719;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0758 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy717 x u D R S_cls f E) ≠
        (nb095AlphaDummy720 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy720;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0759 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy719 D R S_cls E), (nb095AlphaDummy720 x u D R S_cls f E)),
        ((nb095AlphaDummy715 D R S_cls E), (nb095AlphaDummy717 x u D R S_cls f E)),
        ((nb095AlphaDummy716 D R S_cls E), (nb095AlphaDummy718 x u D R S_cls f E)),
        ((nb095AlphaDummy787 D R S_cls E), (nb095AlphaDummy788 x u D R S_cls f E)),
        ((nb095AlphaDummy785 D R S_cls E), (nb095AlphaDummy786 x u D R S_cls f E)),
        ((nb095AlphaDummy662 D R S_cls E), (nb095AlphaDummy664 x u D R S_cls f E)),
        ((nb095AlphaDummy661 D R S_cls E), (nb095AlphaDummy663 x u D R S_cls f E)),
        ((nb095AlphaDummy737 D R S_cls E), (nb095AlphaDummy738 x u D R S_cls f E)),
        ((nb095AlphaDummy665 D R S_cls E), (nb095AlphaDummy666 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy715 D R S_cls E) ≠
        (nb095AlphaDummy719 D R S_cls E) from (by
          unfold nb095AlphaDummy719;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0758 D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy717 x u D R S_cls f E) ≠
        (nb095AlphaDummy720 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy720;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0759 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy715 D R S_cls E) ≠
        (nb095AlphaDummy719 D R S_cls E) from (by
          unfold nb095AlphaDummy719;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0758 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy717 x u D R S_cls f E) ≠
        (nb095AlphaDummy720 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy720;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0759 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy719 D R S_cls E), (nb095AlphaDummy720 x u D R S_cls f E)),
        ((nb095AlphaDummy715 D R S_cls E), (nb095AlphaDummy717 x u D R S_cls f E)),
        ((nb095AlphaDummy716 D R S_cls E), (nb095AlphaDummy718 x u D R S_cls f E)),
        ((nb095AlphaDummy787 D R S_cls E), (nb095AlphaDummy788 x u D R S_cls f E)),
        ((nb095AlphaDummy785 D R S_cls E), (nb095AlphaDummy786 x u D R S_cls f E)),
        ((nb095AlphaDummy662 D R S_cls E), (nb095AlphaDummy664 x u D R S_cls f E)),
        ((nb095AlphaDummy661 D R S_cls E), (nb095AlphaDummy663 x u D R S_cls f E)),
        ((nb095AlphaDummy737 D R S_cls E), (nb095AlphaDummy738 x u D R S_cls f E)),
        ((nb095AlphaDummy665 D R S_cls E), (nb095AlphaDummy666 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed [((nb095AlphaDummy785 D R S_cls E),
                      (nb095AlphaDummy786 x u D R S_cls f E)),
                    ((nb095AlphaDummy662 D R S_cls E),
                      (nb095AlphaDummy664 x u D R S_cls f E)),
                    ((nb095AlphaDummy661 D R S_cls E),
                      (nb095AlphaDummy663 x u D R S_cls f E)),
                    ((nb095AlphaDummy737 D R S_cls E),
                      (nb095AlphaDummy738 x u D R S_cls f E)),
                    ((nb095AlphaDummy665 D R S_cls E),
                      (nb095AlphaDummy666 x u D R S_cls f E)),
                    ((nb095AlphaDummy004 D R S_cls E),
                      (nb095AlphaDummy006 x u D R S_cls f E)),
                    ((nb095AlphaDummy003 D R S_cls E),
                      (nb095AlphaDummy005 x u D R S_cls f E)),
                    ((nb095AlphaDummy001 D R S_cls E), u),
                    ((nb095AlphaDummy002 D R S_cls E), x),
                    ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

theorem nb095_focused_notmem_0072 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy791 D R S_cls E) ∉ S_cls.fv :=
  by
  change
    freshVar
        ((S_cls).fv ∪ ((synCxp (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))))).fv)
        0 ∉
      S_cls.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (hu))

theorem nb095_focused_notmem_0073 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy792 u S_cls E) ∉ S_cls.fv :=
  by
  change
    freshVar
        ((S_cls).fv ∪ ((synCxp (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))
              (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv u)))))).fv)
        0 ∉
      S_cls.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (hu))

theorem nb095_focused_notmem_0074 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy789 D R S_cls E) ∉ S_cls.fv :=
  by
  change
    freshVar
        (((synCnin S_cls (synCxp (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                    (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
                  (synCima (synCcnv (synCdif S_cls (synCid)))
                    (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))))).fv ∪
          ((synCnin S_cls (synCxp (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                    (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
                  (synCima (synCcnv (synCdif S_cls (synCid)))
                    (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))))).fv)
        0 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin S_cls
      (synCxp (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
            (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
          (synCima (synCcnv (synCdif S_cls (synCid)))
            (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0075 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy790 u S_cls E) ∉ S_cls.fv :=
  by
  change
    freshVar
        (((synCnin S_cls (synCxp (synCin E
                  (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))
                (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                    (synCsn (Class.cv u))))))).fv ∪ ((synCnin S_cls (synCxp (synCin E
                  (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))
                (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                    (synCsn (Class.cv u))))))).fv)
        0 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin S_cls
      (synCxp (synCin E
          (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))) (synCin E
          (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0076 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy004 D R S_cls E) ∉ S_cls.fv :=
  by
  change
    freshVar
        (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪ ((synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid)))
                          (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn
                            (Class.cv (nb095AlphaDummy002 D R S_cls E)))))))).fv ∪
              ((synCin S_cls (synCxp (synCin E
                      (synCima (synCcnv (synCdif S_cls (synCid)))
                        (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
                      (synCima (synCcnv (synCdif S_cls (synCid)))
                        (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))))).fv ∪
            ((synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv ∪ ((synCin E
              (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv)
        1 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin S_cls
      (synCxp (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
            (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
          (synCima (synCcnv (synCdif S_cls (synCid)))
            (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0077 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    (nb095AlphaDummy006 x u D R S_cls f E) ∉ S_cls.fv :=
  by
  change
    freshVar
        (((Class.cv f)).fv ∪ ((synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))
                      (synCin D (synCima (synCcnv (synCdif R (synCid)))
                          (synCsn (Class.cv x))))))).fv ∪ ((synCin S_cls (synCxp (synCin E
                      (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))
                    (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                        (synCsn (Class.cv u))))))).fv ∪ ((synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv ∪
          ((synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv u))))).fv)
        1 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin S_cls
      (synCxp (synCin E
          (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))) (synCin E
          (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0078 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy003 D R S_cls E) ∉ S_cls.fv :=
  by
  change
    freshVar
        (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪ ((synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid)))
                          (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn
                            (Class.cv (nb095AlphaDummy002 D R S_cls E)))))))).fv ∪
              ((synCin S_cls (synCxp (synCin E
                      (synCima (synCcnv (synCdif S_cls (synCid)))
                        (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
                      (synCima (synCcnv (synCdif S_cls (synCid)))
                        (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))))).fv ∪
            ((synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv ∪ ((synCin E
              (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv)
        0 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin S_cls
      (synCxp (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
            (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
          (synCima (synCcnv (synCdif S_cls (synCid)))
            (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0079 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    (nb095AlphaDummy005 x u D R S_cls f E) ∉ S_cls.fv :=
  by
  change
    freshVar
        (((Class.cv f)).fv ∪ ((synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))
                      (synCin D (synCima (synCcnv (synCdif R (synCid)))
                          (synCsn (Class.cv x))))))).fv ∪ ((synCin S_cls (synCxp (synCin E
                      (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))
                    (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                        (synCsn (Class.cv u))))))).fv ∪ ((synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv ∪
          ((synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv u))))).fv)
        0 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin S_cls
      (synCxp (synCin E
          (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))) (synCin E
          (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_compact_envfresh_0328 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_S_f : f ∉ S_cls.fv) (dv_S_u : u ∉ S_cls.fv)
    (dv_S_x : x ∉ S_cls.fv) :
    TEnvFresh
      [((nb095AlphaDummy791 D R S_cls E), (nb095AlphaDummy792 u S_cls E)),
        ((nb095AlphaDummy789 D R S_cls E), (nb095AlphaDummy790 u S_cls E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      S_cls.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb095AlphaDummy791 D R S_cls E)
      (nb095AlphaDummy792 u S_cls E) (nb095_focused_notmem_0072 D R S_cls E)
      (nb095_focused_notmem_0073 u S_cls E)
      (TEnvFresh.consFresh (nb095AlphaDummy789 D R S_cls E)
        (nb095AlphaDummy790 u S_cls E) (nb095_focused_notmem_0074 D R S_cls E)
        (nb095_focused_notmem_0075 u S_cls E)
        (TEnvFresh.consFresh (nb095AlphaDummy004 D R S_cls E)
          (nb095AlphaDummy006 x u D R S_cls f E) (nb095_focused_notmem_0076 D R S_cls E)
          (nb095_focused_notmem_0077 x u D R S_cls f E)
          (TEnvFresh.consFresh (nb095AlphaDummy003 D R S_cls E)
            (nb095AlphaDummy005 x u D R S_cls f E) (nb095_focused_notmem_0078 D R S_cls E)
            (nb095_focused_notmem_0079 x u D R S_cls f E)
            (TEnvFresh.consFresh (nb095AlphaDummy001 D R S_cls E) u
              (nb095_focused_notmem_0041 D R S_cls E) dv_S_u
              (TEnvFresh.consFresh (nb095AlphaDummy002 D R S_cls E) x
                (nb095_focused_notmem_0042 D R S_cls E) dv_S_x
                (TEnvFresh.consFresh (nb095AlphaDummy000 D R S_cls E) f
                  (nb095_focused_notmem_0043 D R S_cls E) dv_S_f (TEnvFresh.nil S_cls.fv))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `AlphaSupport.NAR4H5C095M3Part043Stage2`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb095_focused_refl_0009`. -/
@[expose]
noncomputable def nb095FocusedRefl0009 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_S_f : f ∉ S_cls.fv) (dv_S_u : u ∉ S_cls.fv)
    (dv_S_x : x ∉ S_cls.fv) :
    TReflOn
      [((nb095AlphaDummy791 D R S_cls E), (nb095AlphaDummy792 u S_cls E)),
        ((nb095AlphaDummy789 D R S_cls E), (nb095AlphaDummy790 u S_cls E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      S_cls.fv :=
  TEnvFresh.reflOn (nb095_compact_envfresh_0328 x u D R S_cls f E dv_S_f dv_S_u dv_S_x)

theorem nb095_compact_fv_empty_0614 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy794 D R S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0615 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy796 u S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0616 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy793 D R S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0617 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy795 u S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0618 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy797 D R S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0619 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy798 u S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0620 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy791 D R S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0621 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy792 u S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0622 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy789 D R S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0623 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy790 u S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
