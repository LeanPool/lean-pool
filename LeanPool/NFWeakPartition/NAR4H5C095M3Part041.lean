/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C095M3Part040

/-! NF weak partition development: NAR4H5C095M3Part041. -/


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

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0092`. -/
@[expose]
noncomputable def nb095SplitAlpha0092 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_f_u : f ≠ u) (dv_f_x : f ≠ x) :
    TAlphaWff
      [((nb095AlphaDummy667 D R S_cls E), (nb095AlphaDummy668 x u D R S_cls f E)),
        ((nb095AlphaDummy665 D R S_cls E), (nb095AlphaDummy666 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy667 D R S_cls E))
          (Class.cab (nb095AlphaDummy661 D R S_cls E)
            (synWrex (nb095AlphaDummy662 D R S_cls E)
              (synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
                (Class.cv (nb095AlphaDummy003 D R S_cls E)))
              (Wff.classEq (Class.cv (nb095AlphaDummy661 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy667 D R S_cls E))
            (Class.cab (nb095AlphaDummy661 D R S_cls E)
              (synWrex (nb095AlphaDummy662 D R S_cls E)
                (synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
                  (Class.cv (nb095AlphaDummy003 D R S_cls E)))
                (Wff.classEq (Class.cv (nb095AlphaDummy661 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy668 x u D R S_cls f E))
          (Class.cab (nb095AlphaDummy663 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy664 x u D R S_cls f E)
              (synCfv (Class.cv f) (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)))
              (Wff.classEq (Class.cv (nb095AlphaDummy663 x u D R S_cls f E))
                (synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy668 x u D R S_cls f E))
            (Class.cab (nb095AlphaDummy663 x u D R S_cls f E)
              (synWrex (nb095AlphaDummy664 x u D R S_cls f E) (synCfv (Class.cv f)
                  (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)))
                (Wff.classEq (Class.cv (nb095AlphaDummy663 x u D R S_cls f E))
                  (synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
                        (freshVar_injective (((Class.cab (nb095AlphaDummy671 D R S_cls E)
                              (Wff.classEq (Class.cab (nb095AlphaDummy669 D R S_cls E)
                                  (synWbr (Class.cv (nb095AlphaDummy003 D R S_cls E))
                                    (Class.cv (nb095AlphaDummy000 D R S_cls E))
                                    (Class.cv (nb095AlphaDummy669 D R S_cls E)))) (synCsn
                                  (Class.cv (nb095AlphaDummy671 D R S_cls E)))))).fv)
                          (by decide)) (freshVar_injective
                          (((Class.cab (nb095AlphaDummy672 x u D R S_cls f E) (Wff.classEq
                                (Class.cab (nb095AlphaDummy670 x u D R S_cls f E) (synWbr
                                    (Class.cv (nb095AlphaDummy005 x u D R S_cls f E))
                                    (Class.cv f)
                                    (Class.cv (nb095AlphaDummy670 x u D R S_cls f E))))
                                (synCsn (Class.cv
                                    (nb095AlphaDummy672 x u D R S_cls f E)))))).fv)
                          (by decide)) (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.classMem (TAlphaClass.cab
                                (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0090 x u D R S_cls f E))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy669 D R S_cls E) ≠ (nb095AlphaDummy678 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0730
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy670 x u D R S_cls f E) ≠
        (nb095AlphaDummy680 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy680;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0732
                    x u D R S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy669 D R S_cls E) ≠
        (nb095AlphaDummy677 D R S_cls E) from (by
          unfold
            nb095AlphaDummy677;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0730
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy670 x u D R S_cls f E) ≠
        (nb095AlphaDummy679 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0732
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy669 D R S_cls E) ≠
        (nb095AlphaDummy707 D R S_cls E) from (by
          unfold
            nb095AlphaDummy707;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0734
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy670 x u D R S_cls f E) ≠
        (nb095AlphaDummy708 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy708;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0735
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy669 D R S_cls E) ≠
        (nb095AlphaDummy681 D R S_cls E) from (by
          unfold
            nb095AlphaDummy681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0731
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy670 x u D R S_cls f E) ≠ (nb095AlphaDummy682
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0733
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy003 D
        R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy669 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy005 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy670 x u D R S_cls f E))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0091 x u D R S_cls f E)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy709 D R S_cls E), (nb095AlphaDummy710 x u D R S_cls f E)),
        ((nb095AlphaDummy678 D R S_cls E), (nb095AlphaDummy680 x u D R S_cls f E)),
        ((nb095AlphaDummy677 D R S_cls E), (nb095AlphaDummy679 x u D R S_cls f E)),
        ((nb095AlphaDummy707 D R S_cls E), (nb095AlphaDummy708 x u D R S_cls f E)),
        ((nb095AlphaDummy681 D R S_cls E), (nb095AlphaDummy682 x u D R S_cls f E)),
        ((nb095AlphaDummy669 D R S_cls E), (nb095AlphaDummy670 x u D R S_cls f E)),
        ((nb095AlphaDummy671 D R S_cls E), (nb095AlphaDummy672 x u D R S_cls f E)),
        ((nb095AlphaDummy674 D R S_cls E), (nb095AlphaDummy676 x u D R S_cls f E)),
        ((nb095AlphaDummy673 D R S_cls E), (nb095AlphaDummy675 x u D R S_cls f E)),
        ((nb095AlphaDummy662 D R S_cls E), (nb095AlphaDummy664 x u D R S_cls f E)),
        ((nb095AlphaDummy661 D R S_cls E), (nb095AlphaDummy663 x u D R S_cls f E)),
        ((nb095AlphaDummy667 D R S_cls E), (nb095AlphaDummy668 x u D R S_cls f E)),
        ((nb095AlphaDummy665 D R S_cls E), (nb095AlphaDummy666 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy669 D R S_cls E) ≠ (nb095AlphaDummy678 D R S_cls E) from (by
          unfold
            nb095AlphaDummy678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0730
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy670 x u D R S_cls f E) ≠
        (nb095AlphaDummy680 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy680;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0732
                    x u D R S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy669 D R S_cls E) ≠
        (nb095AlphaDummy677 D R S_cls E) from (by
          unfold
            nb095AlphaDummy677;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0730
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy670 x u D R S_cls f E) ≠
        (nb095AlphaDummy679 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0732
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy669 D R S_cls E) ≠
        (nb095AlphaDummy707 D R S_cls E) from (by
          unfold
            nb095AlphaDummy707;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0734
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy670 x u D R S_cls f E) ≠
        (nb095AlphaDummy708 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy708;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0735
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy669 D R S_cls E) ≠
        (nb095AlphaDummy681 D R S_cls E) from (by
          unfold
            nb095AlphaDummy681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0731
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy670 x u D R S_cls f E) ≠ (nb095AlphaDummy682
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0733
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy003 D
        R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy669 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy005 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy670 x u D R S_cls f E))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0091 x u D R S_cls f E)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy709 D R S_cls E), (nb095AlphaDummy710 x u D R S_cls f E)),
        ((nb095AlphaDummy678 D R S_cls E), (nb095AlphaDummy680 x u D R S_cls f E)),
        ((nb095AlphaDummy677 D R S_cls E), (nb095AlphaDummy679 x u D R S_cls f E)),
        ((nb095AlphaDummy707 D R S_cls E), (nb095AlphaDummy708 x u D R S_cls f E)),
        ((nb095AlphaDummy681 D R S_cls E), (nb095AlphaDummy682 x u D R S_cls f E)),
        ((nb095AlphaDummy669 D R S_cls E), (nb095AlphaDummy670 x u D R S_cls f E)),
        ((nb095AlphaDummy671 D R S_cls E), (nb095AlphaDummy672 x u D R S_cls f E)),
        ((nb095AlphaDummy674 D R S_cls E), (nb095AlphaDummy676 x u D R S_cls f E)),
        ((nb095AlphaDummy673 D R S_cls E), (nb095AlphaDummy675 x u D R S_cls f E)),
        ((nb095AlphaDummy662 D R S_cls E), (nb095AlphaDummy664 x u D R S_cls f E)),
        ((nb095AlphaDummy661 D R S_cls E), (nb095AlphaDummy663 x u D R S_cls f E)),
        ((nb095AlphaDummy667 D R S_cls E), (nb095AlphaDummy668 x u D R S_cls f E)),
        ((nb095AlphaDummy665 D R S_cls E), (nb095AlphaDummy666 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy000 D R S_cls E) ≠
                                      (nb095AlphaDummy669 D R S_cls E) from (by
                                      unfold nb095AlphaDummy669;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0748 D R S_cls E) 0))))
                                  (show f ≠ (nb095AlphaDummy670 x u D R S_cls f E) from (by
                                      unfold nb095AlphaDummy670;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0751 x u D R S_cls f E)
                                              0)))) (TAlphaVar.there (show
                                      (nb095AlphaDummy000 D R S_cls E) ≠
                                        (nb095AlphaDummy671 D R S_cls E) from (by
                                        unfold nb095AlphaDummy671;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0749 D R S_cls E) 0))))
                                    (show f ≠ (nb095AlphaDummy672 x u D R S_cls f E) from (by
                                        unfold nb095AlphaDummy672;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0752 x u D R S_cls f E)
                                                0)))) (TAlphaVar.there (show
                                        (nb095AlphaDummy000 D R S_cls E) ≠
        (nb095AlphaDummy674 D R S_cls E) from (by
                                          unfold nb095AlphaDummy674;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0750 D R S_cls E)
                                                  1))))
                                      (show f ≠ (nb095AlphaDummy676 x u D R S_cls f E) from
                                        (by
                                          unfold nb095AlphaDummy676;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0753 x u D R S_cls f
                                                    E)
                                                  1)))) (TAlphaVar.there (show
        (nb095AlphaDummy000 D R S_cls E) ≠ (nb095AlphaDummy673 D R S_cls E) from (by
          unfold nb095AlphaDummy673;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0750 D R S_cls E)
                  0)))) (show f ≠ (nb095AlphaDummy675 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0753 x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
        (nb095AlphaDummy662 D R S_cls E) from (by
          unfold nb095AlphaDummy662;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0742 D R S_cls E)
                  1)))) (show f ≠ (nb095AlphaDummy664 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy664;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0744 x u D R
                    S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
        (nb095AlphaDummy661 D R S_cls E) from (by
          unfold nb095AlphaDummy661;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0742 D R S_cls
                    E)
                  0)))) (show f ≠ (nb095AlphaDummy663 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy663;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0744 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
        (nb095AlphaDummy667 D R S_cls E) from (by
          unfold nb095AlphaDummy667;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0746 D R
                    S_cls E)
                  0)))) (show f ≠ (nb095AlphaDummy668 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy668;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0747 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
        (nb095AlphaDummy665 D R S_cls E) from (by
          unfold nb095AlphaDummy665;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0743 D R
                    S_cls E)
                  0)))) (show f ≠ (nb095AlphaDummy666 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy666;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0745 x u D
                    R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
        (nb095AlphaDummy004 D R S_cls E) from (by
          unfold nb095AlphaDummy004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0740 D R
                    S_cls E)
                  1)))) (show f ≠ (nb095AlphaDummy006 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0741 x u
                    D R S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
        (nb095AlphaDummy003 D R S_cls E) from (by
          unfold nb095AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0740 D
                    R S_cls E)
                  0)))) (show f ≠ (nb095AlphaDummy005 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0741 x
                    u D R S_cls f E)
                  0)))) (TAlphaVar.there (freshVar_injective ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪
        (E).fv) (by decide)) dv_f_u (TAlphaVar.there (freshVar_injective
        ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) (by decide)) dv_f_x (TAlphaVar.here _ _
        _)))))))))))))))) (TAlphaClass.cab
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy671 D R S_cls E) ≠
                                      (nb095AlphaDummy713 D R S_cls E) from (by
                                      unfold nb095AlphaDummy713;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0754 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy672 x u D R S_cls f E) ≠
                                      (nb095AlphaDummy714 x u D R S_cls f E) from (by
                                      unfold nb095AlphaDummy714;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0755 x u D R S_cls f E)
                                              0)))) (TAlphaVar.here _ _ _))))))))))))
            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
                          (Class.cv (nb095AlphaDummy003 D R S_cls E)))).fv ∪
                      ((synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
                          (Class.cv (nb095AlphaDummy004 D R S_cls E)))).fv) (by decide))
                  (freshVar_injective (((synCfv (Class.cv f)
                          (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)))).fv ∪
                      ((synCfv (Class.cv f)
                          (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cv (TAlphaVar.there (show
                            (nb095AlphaDummy662 D R S_cls E) ≠
                              (nb095AlphaDummy715 D R S_cls E) from (by
                              unfold nb095AlphaDummy715;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0756 D R S_cls E)
                                      0)))) (show (nb095AlphaDummy664 x u D R S_cls f E) ≠
                              (nb095AlphaDummy717 x u D R S_cls f E) from (by
                              unfold nb095AlphaDummy717;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb095_support_mem_0757 x u D R S_cls f E) 0))))
                          (TAlphaVar.there (show (nb095AlphaDummy662 D R S_cls E) ≠
                                (nb095AlphaDummy716 D R S_cls E) from (by
                                unfold nb095AlphaDummy716;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0756 D R S_cls E) 1)))) (show
                              (nb095AlphaDummy664 x u D R S_cls f E) ≠
                                (nb095AlphaDummy718 x u D R S_cls f E) from (by
                                unfold nb095AlphaDummy718;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0757 x u D R S_cls f E) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095AlphaDummy662 D R S_cls E))).fv) (by decide))
                          (freshVar_injective
                            (((Class.cv (nb095AlphaDummy664 x u D R S_cls f E))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy715 D R S_cls E) ≠
        (nb095AlphaDummy722 D R S_cls E) from (by
          unfold nb095AlphaDummy722;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0760 D R S_cls
                    E)
                  1)))) (show (nb095AlphaDummy717 x u D R S_cls f E) ≠
        (nb095AlphaDummy725 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy725;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0761 x u D R
                    S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy715 D R S_cls E) ≠
        (nb095AlphaDummy721 D R S_cls E) from (by
          unfold nb095AlphaDummy721;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0760 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy717 x u D R S_cls f E) ≠
        (nb095AlphaDummy724 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy724;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0761 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy715 D R S_cls E) ≠
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
                  (nb095_support_mem_0759 x u D
                    R S_cls f E)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy723 D R S_cls E), (nb095AlphaDummy726 x u D R S_cls f E)),
        ((nb095AlphaDummy722 D R S_cls E), (nb095AlphaDummy725 x u D R S_cls f E)),
        ((nb095AlphaDummy721 D R S_cls E), (nb095AlphaDummy724 x u D R S_cls f E)),
        ((nb095AlphaDummy719 D R S_cls E), (nb095AlphaDummy720 x u D R S_cls f E)),
        ((nb095AlphaDummy715 D R S_cls E), (nb095AlphaDummy717 x u D R S_cls f E)),
        ((nb095AlphaDummy716 D R S_cls E), (nb095AlphaDummy718 x u D R S_cls f E)),
        ((nb095AlphaDummy662 D R S_cls E), (nb095AlphaDummy664 x u D R S_cls f E)),
        ((nb095AlphaDummy661 D R S_cls E), (nb095AlphaDummy663 x u D R S_cls f E)),
        ((nb095AlphaDummy667 D R S_cls E), (nb095AlphaDummy668 x u D R S_cls f E)),
        ((nb095AlphaDummy665 D R S_cls E), (nb095AlphaDummy666 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy722
        D R S_cls E) ≠ (nb095AlphaDummy729 D R S_cls E) from (by
          unfold
            nb095AlphaDummy729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0764
                    D R S_cls
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
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy722 D R S_cls E) ≠
        (nb095AlphaDummy727 D R S_cls E) from (by
          unfold
            nb095AlphaDummy727;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0762
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy725 x u D R S_cls f E) ≠ (nb095AlphaDummy728
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy728;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0763
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy715
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy717 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy723 D R S_cls E) ≠
        (nb095AlphaDummy729 D R S_cls E) from (by
          unfold
            nb095AlphaDummy729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0768
                    D R S_cls
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
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy723 D R S_cls E) ≠
        (nb095AlphaDummy727 D R S_cls E) from (by
          unfold
            nb095AlphaDummy727;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0766
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy726 x u D R S_cls f E) ≠ (nb095AlphaDummy728
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy728;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0767
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy722 D R S_cls E) ≠ (nb095AlphaDummy729
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0764
                    D R S_cls
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
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy722 D R S_cls E) ≠
        (nb095AlphaDummy727 D R S_cls E) from (by
          unfold
            nb095AlphaDummy727;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0762
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy725 x u D R S_cls f E) ≠ (nb095AlphaDummy728
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy728;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0763
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy715
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy717 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy723 D R S_cls E) ≠
        (nb095AlphaDummy729 D R S_cls E) from (by
          unfold
            nb095AlphaDummy729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0768
                    D R S_cls
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
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy723 D R S_cls E) ≠
        (nb095AlphaDummy727 D R S_cls E) from (by
          unfold
            nb095AlphaDummy727;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0766
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy726 x u D R S_cls f E) ≠ (nb095AlphaDummy728
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy728;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0767
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy723 D R S_cls E), (nb095AlphaDummy726 x u D R S_cls f E)),
        ((nb095AlphaDummy722 D R S_cls E), (nb095AlphaDummy725 x u D R S_cls f E)),
        ((nb095AlphaDummy721 D R S_cls E), (nb095AlphaDummy724 x u D R S_cls f E)),
        ((nb095AlphaDummy719 D R S_cls E), (nb095AlphaDummy720 x u D R S_cls f E)),
        ((nb095AlphaDummy715 D R S_cls E), (nb095AlphaDummy717 x u D R S_cls f E)),
        ((nb095AlphaDummy716 D R S_cls E), (nb095AlphaDummy718 x u D R S_cls f E)),
        ((nb095AlphaDummy662 D R S_cls E), (nb095AlphaDummy664 x u D R S_cls f E)),
        ((nb095AlphaDummy661 D R S_cls E), (nb095AlphaDummy663 x u D R S_cls f E)),
        ((nb095AlphaDummy667 D R S_cls E), (nb095AlphaDummy668 x u D R S_cls f E)),
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
                    D R S_cls
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
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy722 D R S_cls E) ≠
        (nb095AlphaDummy731 D R S_cls E) from (by
          unfold
            nb095AlphaDummy731;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0770
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy725 x u D R S_cls f E) ≠ (nb095AlphaDummy732
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy732;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0771
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy715
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy717 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy722 D R S_cls E) ≠
        (nb095AlphaDummy733 D R S_cls E) from (by
          unfold
            nb095AlphaDummy733;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0772
                    D R S_cls
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
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy722 D R S_cls E) ≠
        (nb095AlphaDummy731 D R S_cls E) from (by
          unfold
            nb095AlphaDummy731;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0770
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy725 x u D R S_cls f E) ≠ (nb095AlphaDummy732
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy732;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0771
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy715
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy717 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy723 D R S_cls E) ≠ (nb095AlphaDummy735
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0776
                    D R S_cls
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
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy723 D R S_cls E) ≠
        (nb095AlphaDummy731 D R S_cls E) from (by
          unfold
            nb095AlphaDummy731;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0774
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy726 x u D R S_cls f E) ≠ (nb095AlphaDummy732
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy732;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0775
                    x u D R
                    S_cls f
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
                    D R S_cls
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
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy723 D R S_cls E) ≠
        (nb095AlphaDummy731 D R S_cls E) from (by
          unfold
            nb095AlphaDummy731;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0774
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy726 x u D R S_cls f E) ≠ (nb095AlphaDummy732
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy732;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0775
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy715 D R S_cls E) ≠
                                        (nb095AlphaDummy719 D R S_cls E) from (by
                                        unfold nb095AlphaDummy719;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0758 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy717 x u D R S_cls f E) ≠
                                        (nb095AlphaDummy720 x u D R S_cls f E) from (by
                                        unfold nb095AlphaDummy720;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0759 x u D R S_cls f E)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy719 D R S_cls E),
                                      (nb095AlphaDummy720 x u D R S_cls f E)),
                                    ((nb095AlphaDummy715 D R S_cls E),
                                      (nb095AlphaDummy717 x u D R S_cls f E)),
                                    ((nb095AlphaDummy716 D R S_cls E),
                                      (nb095AlphaDummy718 x u D R S_cls f E)),
                                    ((nb095AlphaDummy662 D R S_cls E),
                                      (nb095AlphaDummy664 x u D R S_cls f E)),
                                    ((nb095AlphaDummy661 D R S_cls E),
                                      (nb095AlphaDummy663 x u D R S_cls f E)),
                                    ((nb095AlphaDummy667 D R S_cls E),
                                      (nb095AlphaDummy668 x u D R S_cls f E)),
                                    ((nb095AlphaDummy665 D R S_cls E),
                                      (nb095AlphaDummy666 x u D R S_cls f E)),
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
                                    (nb095AlphaDummy715 D R S_cls E) ≠
                                      (nb095AlphaDummy719 D R S_cls E) from (by
                                      unfold nb095AlphaDummy719;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0758 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy717 x u D R S_cls f E) ≠
                                      (nb095AlphaDummy720 x u D R S_cls f E) from (by
                                      unfold nb095AlphaDummy720;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0759 x u D R S_cls f E)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy715 D R S_cls E) ≠
                                        (nb095AlphaDummy719 D R S_cls E) from (by
                                        unfold nb095AlphaDummy719;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0758 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy717 x u D R S_cls f E) ≠
                                        (nb095AlphaDummy720 x u D R S_cls f E) from (by
                                        unfold nb095AlphaDummy720;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0759 x u D R S_cls f E)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy719 D R S_cls E),
                                      (nb095AlphaDummy720 x u D R S_cls f E)),
                                    ((nb095AlphaDummy715 D R S_cls E),
                                      (nb095AlphaDummy717 x u D R S_cls f E)),
                                    ((nb095AlphaDummy716 D R S_cls E),
                                      (nb095AlphaDummy718 x u D R S_cls f E)),
                                    ((nb095AlphaDummy662 D R S_cls E),
                                      (nb095AlphaDummy664 x u D R S_cls f E)),
                                    ((nb095AlphaDummy661 D R S_cls E),
                                      (nb095AlphaDummy663 x u D R S_cls f E)),
                                    ((nb095AlphaDummy667 D R S_cls E),
                                      (nb095AlphaDummy668 x u D R S_cls f E)),
                                    ((nb095AlphaDummy665 D R S_cls E),
                                      (nb095AlphaDummy666 x u D R S_cls f E)),
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
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
                          (freshVar_injective (((Class.cab (nb095AlphaDummy671 D R S_cls E)
                                (Wff.classEq (Class.cab (nb095AlphaDummy669 D R S_cls E)
                                    (synWbr (Class.cv (nb095AlphaDummy003 D R S_cls E))
                                      (Class.cv (nb095AlphaDummy000 D R S_cls E))
                                      (Class.cv (nb095AlphaDummy669 D R S_cls E)))) (synCsn
                                    (Class.cv (nb095AlphaDummy671 D R S_cls E)))))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cab (nb095AlphaDummy672 x u D R S_cls f E) (Wff.classEq
                                  (Class.cab (nb095AlphaDummy670 x u D R S_cls f E) (synWbr
                                      (Class.cv (nb095AlphaDummy005 x u D R S_cls f E))
                                      (Class.cv f) (Class.cv
                                        (nb095AlphaDummy670 x u D R S_cls f E)))) (synCsn
                                    (Class.cv (nb095AlphaDummy672 x u D R S_cls f E)))))).fv)
                            (by decide)) (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.classMem
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0090 x u D R S_cls f E)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy669 D R S_cls E) ≠ (nb095AlphaDummy678 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0730
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy670 x u D R S_cls f E) ≠
        (nb095AlphaDummy680 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy680;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0732
                    x u D R S_cls f
                    E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy669 D R S_cls E) ≠
        (nb095AlphaDummy677 D R S_cls E) from (by
          unfold
            nb095AlphaDummy677;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0730
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy670 x u D R S_cls f E) ≠
        (nb095AlphaDummy679 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0732
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy669 D R S_cls E) ≠
        (nb095AlphaDummy707 D R S_cls E) from (by
          unfold
            nb095AlphaDummy707;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0734
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy670 x u D R S_cls f E) ≠ (nb095AlphaDummy708
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy708;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0735
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy669 D R S_cls E) ≠
        (nb095AlphaDummy681 D R S_cls E) from (by
          unfold
            nb095AlphaDummy681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0731
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy670 x u D R S_cls f E) ≠ (nb095AlphaDummy682
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0733
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy003
        D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy669 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy005 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy670 x u D R S_cls f E))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0091 x u D R S_cls f E)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy709 D R S_cls E), (nb095AlphaDummy710 x u D R S_cls f E)),
        ((nb095AlphaDummy678 D R S_cls E), (nb095AlphaDummy680 x u D R S_cls f E)),
        ((nb095AlphaDummy677 D R S_cls E), (nb095AlphaDummy679 x u D R S_cls f E)),
        ((nb095AlphaDummy707 D R S_cls E), (nb095AlphaDummy708 x u D R S_cls f E)),
        ((nb095AlphaDummy681 D R S_cls E), (nb095AlphaDummy682 x u D R S_cls f E)),
        ((nb095AlphaDummy669 D R S_cls E), (nb095AlphaDummy670 x u D R S_cls f E)),
        ((nb095AlphaDummy671 D R S_cls E), (nb095AlphaDummy672 x u D R S_cls f E)),
        ((nb095AlphaDummy674 D R S_cls E), (nb095AlphaDummy676 x u D R S_cls f E)),
        ((nb095AlphaDummy673 D R S_cls E), (nb095AlphaDummy675 x u D R S_cls f E)),
        ((nb095AlphaDummy662 D R S_cls E), (nb095AlphaDummy664 x u D R S_cls f E)),
        ((nb095AlphaDummy661 D R S_cls E), (nb095AlphaDummy663 x u D R S_cls f E)),
        ((nb095AlphaDummy667 D R S_cls E), (nb095AlphaDummy668 x u D R S_cls f E)),
        ((nb095AlphaDummy665 D R S_cls E), (nb095AlphaDummy666 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy669 D R S_cls E) ≠ (nb095AlphaDummy678 D R S_cls E) from (by
          unfold
            nb095AlphaDummy678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0730
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy670 x u D R S_cls f E) ≠
        (nb095AlphaDummy680 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy680;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0732
                    x u D R S_cls f
                    E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy669 D R S_cls E) ≠
        (nb095AlphaDummy677 D R S_cls E) from (by
          unfold
            nb095AlphaDummy677;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0730
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy670 x u D R S_cls f E) ≠
        (nb095AlphaDummy679 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0732
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy669 D R S_cls E) ≠
        (nb095AlphaDummy707 D R S_cls E) from (by
          unfold
            nb095AlphaDummy707;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0734
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy670 x u D R S_cls f E) ≠ (nb095AlphaDummy708
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy708;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0735
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy669 D R S_cls E) ≠
        (nb095AlphaDummy681 D R S_cls E) from (by
          unfold
            nb095AlphaDummy681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0731
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy670 x u D R S_cls f E) ≠ (nb095AlphaDummy682
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0733
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy003
        D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy669 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy005 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy670 x u D R S_cls f E))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0091 x u D R S_cls f E)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy709 D R S_cls E), (nb095AlphaDummy710 x u D R S_cls f E)),
        ((nb095AlphaDummy678 D R S_cls E), (nb095AlphaDummy680 x u D R S_cls f E)),
        ((nb095AlphaDummy677 D R S_cls E), (nb095AlphaDummy679 x u D R S_cls f E)),
        ((nb095AlphaDummy707 D R S_cls E), (nb095AlphaDummy708 x u D R S_cls f E)),
        ((nb095AlphaDummy681 D R S_cls E), (nb095AlphaDummy682 x u D R S_cls f E)),
        ((nb095AlphaDummy669 D R S_cls E), (nb095AlphaDummy670 x u D R S_cls f E)),
        ((nb095AlphaDummy671 D R S_cls E), (nb095AlphaDummy672 x u D R S_cls f E)),
        ((nb095AlphaDummy674 D R S_cls E), (nb095AlphaDummy676 x u D R S_cls f E)),
        ((nb095AlphaDummy673 D R S_cls E), (nb095AlphaDummy675 x u D R S_cls f E)),
        ((nb095AlphaDummy662 D R S_cls E), (nb095AlphaDummy664 x u D R S_cls f E)),
        ((nb095AlphaDummy661 D R S_cls E), (nb095AlphaDummy663 x u D R S_cls f E)),
        ((nb095AlphaDummy667 D R S_cls E), (nb095AlphaDummy668 x u D R S_cls f E)),
        ((nb095AlphaDummy665 D R S_cls E), (nb095AlphaDummy666 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy000 D R S_cls E) ≠
                                        (nb095AlphaDummy669 D R S_cls E) from (by
                                        unfold nb095AlphaDummy669;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0748 D R S_cls E) 0))))
                                    (show f ≠ (nb095AlphaDummy670 x u D R S_cls f E) from (by
                                        unfold nb095AlphaDummy670;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0751 x u D R S_cls f E)
                                                0)))) (TAlphaVar.there (show
                                        (nb095AlphaDummy000 D R S_cls E) ≠
        (nb095AlphaDummy671 D R S_cls E) from (by
                                          unfold nb095AlphaDummy671;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0749 D R S_cls E)
                                                  0))))
                                      (show f ≠ (nb095AlphaDummy672 x u D R S_cls f E) from
                                        (by
                                          unfold nb095AlphaDummy672;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0752 x u D R S_cls f
                                                    E)
                                                  0)))) (TAlphaVar.there (show
        (nb095AlphaDummy000 D R S_cls E) ≠ (nb095AlphaDummy674 D R S_cls E) from (by
          unfold nb095AlphaDummy674;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0750 D R S_cls E)
                  1)))) (show f ≠ (nb095AlphaDummy676 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy676;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0753 x u D R S_cls
                    f E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
        (nb095AlphaDummy673 D R S_cls E) from (by
          unfold nb095AlphaDummy673;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0750 D R S_cls E)
                  0)))) (show f ≠ (nb095AlphaDummy675 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0753 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
        (nb095AlphaDummy662 D R S_cls E) from (by
          unfold nb095AlphaDummy662;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0742 D R S_cls
                    E)
                  1)))) (show f ≠ (nb095AlphaDummy664 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy664;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0744 x u D R
                    S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
        (nb095AlphaDummy661 D R S_cls E) from (by
          unfold nb095AlphaDummy661;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0742 D R
                    S_cls E)
                  0)))) (show f ≠ (nb095AlphaDummy663 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy663;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0744 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
        (nb095AlphaDummy667 D R S_cls E) from (by
          unfold nb095AlphaDummy667;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0746 D R
                    S_cls E)
                  0)))) (show f ≠ (nb095AlphaDummy668 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy668;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0747 x u D
                    R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
        (nb095AlphaDummy665 D R S_cls E) from (by
          unfold nb095AlphaDummy665;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0743 D R
                    S_cls E)
                  0)))) (show f ≠ (nb095AlphaDummy666 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy666;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0745 x u
                    D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
        (nb095AlphaDummy004 D R S_cls E) from (by
          unfold nb095AlphaDummy004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0740 D
                    R S_cls E)
                  1)))) (show f ≠ (nb095AlphaDummy006 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0741 x
                    u D R S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
        (nb095AlphaDummy003 D R S_cls E) from (by
          unfold nb095AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0740
                    D R S_cls E)
                  0)))) (show f ≠ (nb095AlphaDummy005 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0741
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (freshVar_injective ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪
        (E).fv) (by decide)) dv_f_u (TAlphaVar.there (freshVar_injective ((R).fv ∪ (D).fv ∪
        (S_cls).fv ∪ (E).fv) (by decide)) dv_f_x (TAlphaVar.here _ _ _))))))))))))))))
                            (TAlphaClass.cab
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy671 D R S_cls E) ≠
                                        (nb095AlphaDummy713 D R S_cls E) from (by
                                        unfold nb095AlphaDummy713;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0754 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy672 x u D R S_cls f E) ≠
                                        (nb095AlphaDummy714 x u D R S_cls f E) from (by
                                        unfold nb095AlphaDummy714;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0755 x u D R S_cls f E)
                                                0)))) (TAlphaVar.here _ _ _))))))))))))
              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
                            (Class.cv (nb095AlphaDummy003 D R S_cls E)))).fv ∪
                        ((synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
                            (Class.cv (nb095AlphaDummy004 D R S_cls E)))).fv) (by decide))
                    (freshVar_injective (((synCfv (Class.cv f)
                            (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)))).fv ∪
                        ((synCfv (Class.cv f)
                            (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
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
                                        (nb095_support_mem_0757 x u D R S_cls f E) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy662 D R S_cls E) ≠
                                  (nb095AlphaDummy716 D R S_cls E) from (by
                                  unfold nb095AlphaDummy716;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0756 D R S_cls E) 1)))) (show
                                (nb095AlphaDummy664 x u D R S_cls f E) ≠
                                  (nb095AlphaDummy718 x u D R S_cls f E) from (by
                                  unfold nb095AlphaDummy718;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0757 x u D R S_cls f E) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095AlphaDummy662 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095AlphaDummy664 x u D R S_cls f E))).fv)
                              (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                          (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy715 D R S_cls E) ≠ (nb095AlphaDummy722 D R S_cls E) from (by
          unfold nb095AlphaDummy722;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0760 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy717 x u D R S_cls f E) ≠
        (nb095AlphaDummy725 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy725;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0761 x u D R
                    S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy715 D R S_cls E) ≠
        (nb095AlphaDummy721 D R S_cls E) from (by
          unfold nb095AlphaDummy721;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0760 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy717 x u D R S_cls f E) ≠
        (nb095AlphaDummy724 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy724;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0761 x u D
                    R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy715 D R S_cls E) ≠
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
                  (nb095_support_mem_0759 x u
                    D R S_cls f E)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy723 D R S_cls E), (nb095AlphaDummy726 x u D R S_cls f E)),
        ((nb095AlphaDummy722 D R S_cls E), (nb095AlphaDummy725 x u D R S_cls f E)),
        ((nb095AlphaDummy721 D R S_cls E), (nb095AlphaDummy724 x u D R S_cls f E)),
        ((nb095AlphaDummy719 D R S_cls E), (nb095AlphaDummy720 x u D R S_cls f E)),
        ((nb095AlphaDummy715 D R S_cls E), (nb095AlphaDummy717 x u D R S_cls f E)),
        ((nb095AlphaDummy716 D R S_cls E), (nb095AlphaDummy718 x u D R S_cls f E)),
        ((nb095AlphaDummy662 D R S_cls E), (nb095AlphaDummy664 x u D R S_cls f E)),
        ((nb095AlphaDummy661 D R S_cls E), (nb095AlphaDummy663 x u D R S_cls f E)),
        ((nb095AlphaDummy667 D R S_cls E), (nb095AlphaDummy668 x u D R S_cls f E)),
        ((nb095AlphaDummy665 D R S_cls E), (nb095AlphaDummy666 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy722
        D R S_cls E) ≠ (nb095AlphaDummy729 D R S_cls E) from (by
          unfold
            nb095AlphaDummy729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0764
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy725 x u D R S_cls f E) ≠ (nb095AlphaDummy730
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy730;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0765
                    x u D R
                    S_cls f
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
                    D R
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
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy715
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy717 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy723 D R S_cls E) ≠
        (nb095AlphaDummy729 D R S_cls E) from (by
          unfold
            nb095AlphaDummy729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0768
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy726 x u D R S_cls f E) ≠ (nb095AlphaDummy730
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy730;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0769
                    x u D R
                    S_cls f
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
                    D R
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
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy722 D R S_cls E) ≠ (nb095AlphaDummy729
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0764
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy725 x u D R S_cls f E) ≠ (nb095AlphaDummy730
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy730;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0765
                    x u D R
                    S_cls f
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
                    D R
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
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy715
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy717 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy723 D R S_cls E) ≠
        (nb095AlphaDummy729 D R S_cls E) from (by
          unfold
            nb095AlphaDummy729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0768
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy726 x u D R S_cls f E) ≠ (nb095AlphaDummy730
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy730;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0769
                    x u D R
                    S_cls f
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
                    D R
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
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy723 D R S_cls E), (nb095AlphaDummy726 x u D R S_cls f E)),
        ((nb095AlphaDummy722 D R S_cls E), (nb095AlphaDummy725 x u D R S_cls f E)),
        ((nb095AlphaDummy721 D R S_cls E), (nb095AlphaDummy724 x u D R S_cls f E)),
        ((nb095AlphaDummy719 D R S_cls E), (nb095AlphaDummy720 x u D R S_cls f E)),
        ((nb095AlphaDummy715 D R S_cls E), (nb095AlphaDummy717 x u D R S_cls f E)),
        ((nb095AlphaDummy716 D R S_cls E), (nb095AlphaDummy718 x u D R S_cls f E)),
        ((nb095AlphaDummy662 D R S_cls E), (nb095AlphaDummy664 x u D R S_cls f E)),
        ((nb095AlphaDummy661 D R S_cls E), (nb095AlphaDummy663 x u D R S_cls f E)),
        ((nb095AlphaDummy667 D R S_cls E), (nb095AlphaDummy668 x u D R S_cls f E)),
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
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy725 x u D R S_cls f E) ≠ (nb095AlphaDummy734
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy734;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0773
                    x u D R
                    S_cls f
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
                    D R
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
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy715
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy717 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy722 D R S_cls E) ≠
        (nb095AlphaDummy733 D R S_cls E) from (by
          unfold
            nb095AlphaDummy733;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0772
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy725 x u D R S_cls f E) ≠ (nb095AlphaDummy734
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy734;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0773
                    x u D R
                    S_cls f
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
                    D R
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
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy715
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy717 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy723 D R S_cls E) ≠ (nb095AlphaDummy735
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0776
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy726 x u D R S_cls f E) ≠ (nb095AlphaDummy736
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0777
                    x u D R
                    S_cls f
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
                    D R
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
                    x u D
                    R
                    S_cls
                    f E)
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
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy726 x u D R S_cls f E) ≠ (nb095AlphaDummy736
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0777
                    x u D R
                    S_cls f
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
                    D R
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
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy715 D R S_cls E) ≠
        (nb095AlphaDummy719 D R S_cls E) from (by
                                          unfold nb095AlphaDummy719;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0758 D R S_cls E)
                                                  0)))) (show
                                        (nb095AlphaDummy717 x u D R S_cls f E) ≠
        (nb095AlphaDummy720 x u D R S_cls f E) from (by
                                          unfold nb095AlphaDummy720;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0759 x u D R S_cls f
                                                    E)
                                                  0)))) (TAlphaVar.here _ _ _)))
                                  (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy719 D R S_cls E),
                                        (nb095AlphaDummy720 x u D R S_cls f E)),
                                      ((nb095AlphaDummy715 D R S_cls E),
                                        (nb095AlphaDummy717 x u D R S_cls f E)),
                                      ((nb095AlphaDummy716 D R S_cls E),
                                        (nb095AlphaDummy718 x u D R S_cls f E)),
                                      ((nb095AlphaDummy662 D R S_cls E),
                                        (nb095AlphaDummy664 x u D R S_cls f E)),
                                      ((nb095AlphaDummy661 D R S_cls E),
                                        (nb095AlphaDummy663 x u D R S_cls f E)),
                                      ((nb095AlphaDummy667 D R S_cls E),
                                        (nb095AlphaDummy668 x u D R S_cls f E)),
                                      ((nb095AlphaDummy665 D R S_cls E),
                                        (nb095AlphaDummy666 x u D R S_cls f E)),
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
                                      (nb095AlphaDummy715 D R S_cls E) ≠
                                        (nb095AlphaDummy719 D R S_cls E) from (by
                                        unfold nb095AlphaDummy719;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0758 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy717 x u D R S_cls f E) ≠
                                        (nb095AlphaDummy720 x u D R S_cls f E) from (by
                                        unfold nb095AlphaDummy720;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0759 x u D R S_cls f E)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy715 D R S_cls E) ≠
        (nb095AlphaDummy719 D R S_cls E) from (by
                                          unfold nb095AlphaDummy719;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0758 D R S_cls E)
                                                  0)))) (show
                                        (nb095AlphaDummy717 x u D R S_cls f E) ≠
        (nb095AlphaDummy720 x u D R S_cls f E) from (by
                                          unfold nb095AlphaDummy720;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0759 x u D R S_cls f
                                                    E)
                                                  0)))) (TAlphaVar.here _ _ _)))
                                  (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy719 D R S_cls E),
                                        (nb095AlphaDummy720 x u D R S_cls f E)),
                                      ((nb095AlphaDummy715 D R S_cls E),
                                        (nb095AlphaDummy717 x u D R S_cls f E)),
                                      ((nb095AlphaDummy716 D R S_cls E),
                                        (nb095AlphaDummy718 x u D R S_cls f E)),
                                      ((nb095AlphaDummy662 D R S_cls E),
                                        (nb095AlphaDummy664 x u D R S_cls f E)),
                                      ((nb095AlphaDummy661 D R S_cls E),
                                        (nb095AlphaDummy663 x u D R S_cls f E)),
                                      ((nb095AlphaDummy667 D R S_cls E),
                                        (nb095AlphaDummy668 x u D R S_cls f E)),
                                      ((nb095AlphaDummy665 D R S_cls E),
                                        (nb095AlphaDummy666 x u D R S_cls f E)),
                                      ((nb095AlphaDummy004 D R S_cls E),
                                        (nb095AlphaDummy006 x u D R S_cls f E)),
                                      ((nb095AlphaDummy003 D R S_cls E),
                                        (nb095AlphaDummy005 x u D R S_cls f E)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
