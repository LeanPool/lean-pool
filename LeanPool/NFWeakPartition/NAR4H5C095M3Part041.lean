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

@[expose]
noncomputable def nb095_split_alpha_0092 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_f_u : f ≠ u) (dv_f_x : f ≠ x) :
    TAlphaWff
      [((nb095_alpha_dummy_667 D R S_cls E), (nb095_alpha_dummy_668 x u D R S_cls f E)),
        ((nb095_alpha_dummy_665 D R S_cls E), (nb095_alpha_dummy_666 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_667 D R S_cls E))
          (Class.cab (nb095_alpha_dummy_661 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_662 D R S_cls E)
              (syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_003 D R S_cls E)))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_661 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_667 D R S_cls E))
            (Class.cab (nb095_alpha_dummy_661 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_662 D R S_cls E)
                (syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                  (Class.cv (nb095_alpha_dummy_003 D R S_cls E)))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_661 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_668 x u D R S_cls f E))
          (Class.cab (nb095_alpha_dummy_663 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_664 x u D R S_cls f E)
              (syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_663 x u D R S_cls f E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_668 x u D R S_cls f E))
            (Class.cab (nb095_alpha_dummy_663 x u D R S_cls f E)
              (syn_wrex (nb095_alpha_dummy_664 x u D R S_cls f E) (syn_cfv (Class.cv f)
                  (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_663 x u D R S_cls f E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
                        (freshVar_injective (((Class.cab (nb095_alpha_dummy_671 D R S_cls E)
                              (Wff.classEq (Class.cab (nb095_alpha_dummy_669 D R S_cls E)
                                  (syn_wbr (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
                                    (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                                    (Class.cv (nb095_alpha_dummy_669 D R S_cls E)))) (syn_csn
                                  (Class.cv (nb095_alpha_dummy_671 D R S_cls E)))))).fv)
                          (by decide)) (freshVar_injective
                          (((Class.cab (nb095_alpha_dummy_672 x u D R S_cls f E) (Wff.classEq
                                (Class.cab (nb095_alpha_dummy_670 x u D R S_cls f E) (syn_wbr
                                    (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))
                                    (Class.cv f)
                                    (Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E))))
                                (syn_csn (Class.cv
                                    (nb095_alpha_dummy_672 x u D R S_cls f E)))))).fv)
                          (by decide)) (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.classMem (TAlphaClass.cab
                                (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg
        (nb095_split_alpha_0090 x u D R S_cls f E))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_669 D R S_cls E) ≠ (nb095_alpha_dummy_678 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0730
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_670 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_680 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_680;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0732
                    x u D R S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_669 D R S_cls E) ≠
        (nb095_alpha_dummy_677 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_677;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0730
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_670 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_679 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0732
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_669 D R S_cls E) ≠
        (nb095_alpha_dummy_707 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_707;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0734
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_670 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_708 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_708;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0735
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_669 D R S_cls E) ≠
        (nb095_alpha_dummy_681 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0731
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_670 x u D R S_cls f E) ≠ (nb095_alpha_dummy_682
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0733
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_003 D
        R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_669 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0091 x u D R S_cls f E)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_709 D R S_cls E), (nb095_alpha_dummy_710 x u D R S_cls f E)),
        ((nb095_alpha_dummy_678 D R S_cls E), (nb095_alpha_dummy_680 x u D R S_cls f E)),
        ((nb095_alpha_dummy_677 D R S_cls E), (nb095_alpha_dummy_679 x u D R S_cls f E)),
        ((nb095_alpha_dummy_707 D R S_cls E), (nb095_alpha_dummy_708 x u D R S_cls f E)),
        ((nb095_alpha_dummy_681 D R S_cls E), (nb095_alpha_dummy_682 x u D R S_cls f E)),
        ((nb095_alpha_dummy_669 D R S_cls E), (nb095_alpha_dummy_670 x u D R S_cls f E)),
        ((nb095_alpha_dummy_671 D R S_cls E), (nb095_alpha_dummy_672 x u D R S_cls f E)),
        ((nb095_alpha_dummy_674 D R S_cls E), (nb095_alpha_dummy_676 x u D R S_cls f E)),
        ((nb095_alpha_dummy_673 D R S_cls E), (nb095_alpha_dummy_675 x u D R S_cls f E)),
        ((nb095_alpha_dummy_662 D R S_cls E), (nb095_alpha_dummy_664 x u D R S_cls f E)),
        ((nb095_alpha_dummy_661 D R S_cls E), (nb095_alpha_dummy_663 x u D R S_cls f E)),
        ((nb095_alpha_dummy_667 D R S_cls E), (nb095_alpha_dummy_668 x u D R S_cls f E)),
        ((nb095_alpha_dummy_665 D R S_cls E), (nb095_alpha_dummy_666 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_669 D R S_cls E) ≠ (nb095_alpha_dummy_678 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0730
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_670 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_680 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_680;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0732
                    x u D R S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_669 D R S_cls E) ≠
        (nb095_alpha_dummy_677 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_677;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0730
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_670 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_679 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0732
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_669 D R S_cls E) ≠
        (nb095_alpha_dummy_707 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_707;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0734
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_670 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_708 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_708;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0735
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_669 D R S_cls E) ≠
        (nb095_alpha_dummy_681 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0731
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_670 x u D R S_cls f E) ≠ (nb095_alpha_dummy_682
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0733
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_003 D
        R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_669 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0091 x u D R S_cls f E)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_709 D R S_cls E), (nb095_alpha_dummy_710 x u D R S_cls f E)),
        ((nb095_alpha_dummy_678 D R S_cls E), (nb095_alpha_dummy_680 x u D R S_cls f E)),
        ((nb095_alpha_dummy_677 D R S_cls E), (nb095_alpha_dummy_679 x u D R S_cls f E)),
        ((nb095_alpha_dummy_707 D R S_cls E), (nb095_alpha_dummy_708 x u D R S_cls f E)),
        ((nb095_alpha_dummy_681 D R S_cls E), (nb095_alpha_dummy_682 x u D R S_cls f E)),
        ((nb095_alpha_dummy_669 D R S_cls E), (nb095_alpha_dummy_670 x u D R S_cls f E)),
        ((nb095_alpha_dummy_671 D R S_cls E), (nb095_alpha_dummy_672 x u D R S_cls f E)),
        ((nb095_alpha_dummy_674 D R S_cls E), (nb095_alpha_dummy_676 x u D R S_cls f E)),
        ((nb095_alpha_dummy_673 D R S_cls E), (nb095_alpha_dummy_675 x u D R S_cls f E)),
        ((nb095_alpha_dummy_662 D R S_cls E), (nb095_alpha_dummy_664 x u D R S_cls f E)),
        ((nb095_alpha_dummy_661 D R S_cls E), (nb095_alpha_dummy_663 x u D R S_cls f E)),
        ((nb095_alpha_dummy_667 D R S_cls E), (nb095_alpha_dummy_668 x u D R S_cls f E)),
        ((nb095_alpha_dummy_665 D R S_cls E), (nb095_alpha_dummy_666 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095_alpha_dummy_000 D R S_cls E) ≠
                                      (nb095_alpha_dummy_669 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_669;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0748 D R S_cls E) 0))))
                                  (show f ≠ (nb095_alpha_dummy_670 x u D R S_cls f E) from (by
                                      unfold nb095_alpha_dummy_670;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0751 x u D R S_cls f E)
                                              0)))) (TAlphaVar.there (show
                                      (nb095_alpha_dummy_000 D R S_cls E) ≠
                                        (nb095_alpha_dummy_671 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_671;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0749 D R S_cls E) 0))))
                                    (show f ≠ (nb095_alpha_dummy_672 x u D R S_cls f E) from (by
                                        unfold nb095_alpha_dummy_672;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0752 x u D R S_cls f E)
                                                0)))) (TAlphaVar.there (show
                                        (nb095_alpha_dummy_000 D R S_cls E) ≠
        (nb095_alpha_dummy_674 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_674;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0750 D R S_cls E)
                                                  1))))
                                      (show f ≠ (nb095_alpha_dummy_676 x u D R S_cls f E) from
                                        (by
                                          unfold nb095_alpha_dummy_676;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0753 x u D R S_cls f
                                                    E)
                                                  1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_000 D R S_cls E) ≠ (nb095_alpha_dummy_673 D R S_cls E) from (by
          unfold nb095_alpha_dummy_673;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0750 D R S_cls E)
                  0)))) (show f ≠ (nb095_alpha_dummy_675 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0753 x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_000 D R S_cls E) ≠
        (nb095_alpha_dummy_662 D R S_cls E) from (by
          unfold nb095_alpha_dummy_662;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0742 D R S_cls E)
                  1)))) (show f ≠ (nb095_alpha_dummy_664 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_664;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0744 x u D R
                    S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_000 D R S_cls E) ≠
        (nb095_alpha_dummy_661 D R S_cls E) from (by
          unfold nb095_alpha_dummy_661;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0742 D R S_cls
                    E)
                  0)))) (show f ≠ (nb095_alpha_dummy_663 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_663;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0744 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_000 D R S_cls E) ≠
        (nb095_alpha_dummy_667 D R S_cls E) from (by
          unfold nb095_alpha_dummy_667;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0746 D R
                    S_cls E)
                  0)))) (show f ≠ (nb095_alpha_dummy_668 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_668;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0747 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_000 D R S_cls E) ≠
        (nb095_alpha_dummy_665 D R S_cls E) from (by
          unfold nb095_alpha_dummy_665;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0743 D R
                    S_cls E)
                  0)))) (show f ≠ (nb095_alpha_dummy_666 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_666;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0745 x u D
                    R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_000 D R S_cls E) ≠
        (nb095_alpha_dummy_004 D R S_cls E) from (by
          unfold nb095_alpha_dummy_004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0740 D R
                    S_cls E)
                  1)))) (show f ≠ (nb095_alpha_dummy_006 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0741 x u
                    D R S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_000 D R S_cls E) ≠
        (nb095_alpha_dummy_003 D R S_cls E) from (by
          unfold nb095_alpha_dummy_003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0740 D
                    R S_cls E)
                  0)))) (show f ≠ (nb095_alpha_dummy_005 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_005;
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
                                    (nb095_alpha_dummy_671 D R S_cls E) ≠
                                      (nb095_alpha_dummy_713 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_713;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0754 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_672 x u D R S_cls f E) ≠
                                      (nb095_alpha_dummy_714 x u D R S_cls f E) from (by
                                      unfold nb095_alpha_dummy_714;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0755 x u D R S_cls f E)
                                              0)))) (TAlphaVar.here _ _ _))))))))))))
            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                          (Class.cv (nb095_alpha_dummy_003 D R S_cls E)))).fv ∪
                      ((syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                          (Class.cv (nb095_alpha_dummy_004 D R S_cls E)))).fv) (by decide))
                  (freshVar_injective (((syn_cfv (Class.cv f)
                          (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)))).fv ∪
                      ((syn_cfv (Class.cv f)
                          (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cv (TAlphaVar.there (show
                            (nb095_alpha_dummy_662 D R S_cls E) ≠
                              (nb095_alpha_dummy_715 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_715;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0756 D R S_cls E)
                                      0)))) (show (nb095_alpha_dummy_664 x u D R S_cls f E) ≠
                              (nb095_alpha_dummy_717 x u D R S_cls f E) from (by
                              unfold nb095_alpha_dummy_717;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb095_support_mem_0757 x u D R S_cls f E) 0))))
                          (TAlphaVar.there (show (nb095_alpha_dummy_662 D R S_cls E) ≠
                                (nb095_alpha_dummy_716 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_716;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0756 D R S_cls E) 1)))) (show
                              (nb095_alpha_dummy_664 x u D R S_cls f E) ≠
                                (nb095_alpha_dummy_718 x u D R S_cls f E) from (by
                                unfold nb095_alpha_dummy_718;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0757 x u D R S_cls f E) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095_alpha_dummy_662 D R S_cls E))).fv) (by decide))
                          (freshVar_injective
                            (((Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_715 D R S_cls E) ≠
        (nb095_alpha_dummy_722 D R S_cls E) from (by
          unfold nb095_alpha_dummy_722;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0760 D R S_cls
                    E)
                  1)))) (show (nb095_alpha_dummy_717 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_725 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_725;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0761 x u D R
                    S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_715 D R S_cls E) ≠
        (nb095_alpha_dummy_721 D R S_cls E) from (by
          unfold nb095_alpha_dummy_721;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0760 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_717 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_724 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_724;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0761 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_715 D R S_cls E) ≠
        (nb095_alpha_dummy_719 D R S_cls E) from (by
          unfold nb095_alpha_dummy_719;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0758 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_717 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_720 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_720;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0759 x u D
                    R S_cls f E)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_723 D R S_cls E), (nb095_alpha_dummy_726 x u D R S_cls f E)),
        ((nb095_alpha_dummy_722 D R S_cls E), (nb095_alpha_dummy_725 x u D R S_cls f E)),
        ((nb095_alpha_dummy_721 D R S_cls E), (nb095_alpha_dummy_724 x u D R S_cls f E)),
        ((nb095_alpha_dummy_719 D R S_cls E), (nb095_alpha_dummy_720 x u D R S_cls f E)),
        ((nb095_alpha_dummy_715 D R S_cls E), (nb095_alpha_dummy_717 x u D R S_cls f E)),
        ((nb095_alpha_dummy_716 D R S_cls E), (nb095_alpha_dummy_718 x u D R S_cls f E)),
        ((nb095_alpha_dummy_662 D R S_cls E), (nb095_alpha_dummy_664 x u D R S_cls f E)),
        ((nb095_alpha_dummy_661 D R S_cls E), (nb095_alpha_dummy_663 x u D R S_cls f E)),
        ((nb095_alpha_dummy_667 D R S_cls E), (nb095_alpha_dummy_668 x u D R S_cls f E)),
        ((nb095_alpha_dummy_665 D R S_cls E), (nb095_alpha_dummy_666 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_722
        D R S_cls E) ≠ (nb095_alpha_dummy_729 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0764
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_725 x u D R S_cls f E) ≠ (nb095_alpha_dummy_730
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_730;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0765
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_722 D R S_cls E) ≠
        (nb095_alpha_dummy_727 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_727;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0762
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_725 x u D R S_cls f E) ≠ (nb095_alpha_dummy_728
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_728;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0763
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_715
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_717 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_723 D R S_cls E) ≠
        (nb095_alpha_dummy_729 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0768
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_726 x u D R S_cls f E) ≠ (nb095_alpha_dummy_730
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_730;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0769
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_723 D R S_cls E) ≠
        (nb095_alpha_dummy_727 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_727;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0766
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_726 x u D R S_cls f E) ≠ (nb095_alpha_dummy_728
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_728;
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
        (TAlphaVar.there (show (nb095_alpha_dummy_722 D R S_cls E) ≠ (nb095_alpha_dummy_729
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0764
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_725 x u D R S_cls f E) ≠ (nb095_alpha_dummy_730
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_730;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0765
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_722 D R S_cls E) ≠
        (nb095_alpha_dummy_727 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_727;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0762
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_725 x u D R S_cls f E) ≠ (nb095_alpha_dummy_728
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_728;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0763
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_715
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_717 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_723 D R S_cls E) ≠
        (nb095_alpha_dummy_729 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0768
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_726 x u D R S_cls f E) ≠ (nb095_alpha_dummy_730
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_730;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0769
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_723 D R S_cls E) ≠
        (nb095_alpha_dummy_727 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_727;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0766
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_726 x u D R S_cls f E) ≠ (nb095_alpha_dummy_728
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_728;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0767
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_723 D R S_cls E), (nb095_alpha_dummy_726 x u D R S_cls f E)),
        ((nb095_alpha_dummy_722 D R S_cls E), (nb095_alpha_dummy_725 x u D R S_cls f E)),
        ((nb095_alpha_dummy_721 D R S_cls E), (nb095_alpha_dummy_724 x u D R S_cls f E)),
        ((nb095_alpha_dummy_719 D R S_cls E), (nb095_alpha_dummy_720 x u D R S_cls f E)),
        ((nb095_alpha_dummy_715 D R S_cls E), (nb095_alpha_dummy_717 x u D R S_cls f E)),
        ((nb095_alpha_dummy_716 D R S_cls E), (nb095_alpha_dummy_718 x u D R S_cls f E)),
        ((nb095_alpha_dummy_662 D R S_cls E), (nb095_alpha_dummy_664 x u D R S_cls f E)),
        ((nb095_alpha_dummy_661 D R S_cls E), (nb095_alpha_dummy_663 x u D R S_cls f E)),
        ((nb095_alpha_dummy_667 D R S_cls E), (nb095_alpha_dummy_668 x u D R S_cls f E)),
        ((nb095_alpha_dummy_665 D R S_cls E), (nb095_alpha_dummy_666 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_715 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_717 x u D R S_cls f E))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_715 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_717 x u D R S_cls f E))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_722
        D R S_cls E) ≠ (nb095_alpha_dummy_733 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_733;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0772
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_725 x u D R S_cls f E) ≠ (nb095_alpha_dummy_734
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_734;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0773
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_722 D R S_cls E) ≠
        (nb095_alpha_dummy_731 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_731;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0770
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_725 x u D R S_cls f E) ≠ (nb095_alpha_dummy_732
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_732;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0771
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_715
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_717 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_722 D R S_cls E) ≠
        (nb095_alpha_dummy_733 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_733;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0772
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_725 x u D R S_cls f E) ≠ (nb095_alpha_dummy_734
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_734;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0773
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_722 D R S_cls E) ≠
        (nb095_alpha_dummy_731 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_731;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0770
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_725 x u D R S_cls f E) ≠ (nb095_alpha_dummy_732
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_732;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0771
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_715
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_717 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_723 D R S_cls E) ≠ (nb095_alpha_dummy_735
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0776
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_726 x u D R S_cls f E) ≠ (nb095_alpha_dummy_736
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0777
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_723 D R S_cls E) ≠
        (nb095_alpha_dummy_731 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_731;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0774
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_726 x u D R S_cls f E) ≠ (nb095_alpha_dummy_732
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_732;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0775
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_723
        D R S_cls E) ≠ (nb095_alpha_dummy_735 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0776
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_726 x u D R S_cls f E) ≠ (nb095_alpha_dummy_736
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0777
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_723 D R S_cls E) ≠
        (nb095_alpha_dummy_731 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_731;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0774
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_726 x u D R S_cls f E) ≠ (nb095_alpha_dummy_732
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_732;
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
                                      (nb095_alpha_dummy_715 D R S_cls E) ≠
                                        (nb095_alpha_dummy_719 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_719;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0758 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_717 x u D R S_cls f E) ≠
                                        (nb095_alpha_dummy_720 x u D R S_cls f E) from (by
                                        unfold nb095_alpha_dummy_720;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0759 x u D R S_cls f E)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb095_alpha_dummy_719 D R S_cls E),
                                      (nb095_alpha_dummy_720 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_715 D R S_cls E),
                                      (nb095_alpha_dummy_717 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_716 D R S_cls E),
                                      (nb095_alpha_dummy_718 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_662 D R S_cls E),
                                      (nb095_alpha_dummy_664 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_661 D R S_cls E),
                                      (nb095_alpha_dummy_663 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_667 D R S_cls E),
                                      (nb095_alpha_dummy_668 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_665 D R S_cls E),
                                      (nb095_alpha_dummy_666 x u D R S_cls f E)),
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
                                    (nb095_alpha_dummy_715 D R S_cls E) ≠
                                      (nb095_alpha_dummy_719 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_719;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0758 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_717 x u D R S_cls f E) ≠
                                      (nb095_alpha_dummy_720 x u D R S_cls f E) from (by
                                      unfold nb095_alpha_dummy_720;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0759 x u D R S_cls f E)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_715 D R S_cls E) ≠
                                        (nb095_alpha_dummy_719 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_719;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0758 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_717 x u D R S_cls f E) ≠
                                        (nb095_alpha_dummy_720 x u D R S_cls f E) from (by
                                        unfold nb095_alpha_dummy_720;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0759 x u D R S_cls f E)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb095_alpha_dummy_719 D R S_cls E),
                                      (nb095_alpha_dummy_720 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_715 D R S_cls E),
                                      (nb095_alpha_dummy_717 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_716 D R S_cls E),
                                      (nb095_alpha_dummy_718 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_662 D R S_cls E),
                                      (nb095_alpha_dummy_664 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_661 D R S_cls E),
                                      (nb095_alpha_dummy_663 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_667 D R S_cls E),
                                      (nb095_alpha_dummy_668 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_665 D R S_cls E),
                                      (nb095_alpha_dummy_666 x u D R S_cls f E)),
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
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
                          (freshVar_injective (((Class.cab (nb095_alpha_dummy_671 D R S_cls E)
                                (Wff.classEq (Class.cab (nb095_alpha_dummy_669 D R S_cls E)
                                    (syn_wbr (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
                                      (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                                      (Class.cv (nb095_alpha_dummy_669 D R S_cls E)))) (syn_csn
                                    (Class.cv (nb095_alpha_dummy_671 D R S_cls E)))))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cab (nb095_alpha_dummy_672 x u D R S_cls f E) (Wff.classEq
                                  (Class.cab (nb095_alpha_dummy_670 x u D R S_cls f E) (syn_wbr
                                      (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))
                                      (Class.cv f) (Class.cv
                                        (nb095_alpha_dummy_670 x u D R S_cls f E)))) (syn_csn
                                    (Class.cv (nb095_alpha_dummy_672 x u D R S_cls f E)))))).fv)
                            (by decide)) (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.classMem
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0090 x u D R S_cls f E)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_669 D R S_cls E) ≠ (nb095_alpha_dummy_678 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0730
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_670 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_680 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_680;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0732
                    x u D R S_cls f
                    E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_669 D R S_cls E) ≠
        (nb095_alpha_dummy_677 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_677;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0730
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_670 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_679 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0732
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_669 D R S_cls E) ≠
        (nb095_alpha_dummy_707 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_707;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0734
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_670 x u D R S_cls f E) ≠ (nb095_alpha_dummy_708
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_708;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0735
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_669 D R S_cls E) ≠
        (nb095_alpha_dummy_681 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0731
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_670 x u D R S_cls f E) ≠ (nb095_alpha_dummy_682
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0733
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_003
        D R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_669 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0091 x u D R S_cls f E)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_709 D R S_cls E), (nb095_alpha_dummy_710 x u D R S_cls f E)),
        ((nb095_alpha_dummy_678 D R S_cls E), (nb095_alpha_dummy_680 x u D R S_cls f E)),
        ((nb095_alpha_dummy_677 D R S_cls E), (nb095_alpha_dummy_679 x u D R S_cls f E)),
        ((nb095_alpha_dummy_707 D R S_cls E), (nb095_alpha_dummy_708 x u D R S_cls f E)),
        ((nb095_alpha_dummy_681 D R S_cls E), (nb095_alpha_dummy_682 x u D R S_cls f E)),
        ((nb095_alpha_dummy_669 D R S_cls E), (nb095_alpha_dummy_670 x u D R S_cls f E)),
        ((nb095_alpha_dummy_671 D R S_cls E), (nb095_alpha_dummy_672 x u D R S_cls f E)),
        ((nb095_alpha_dummy_674 D R S_cls E), (nb095_alpha_dummy_676 x u D R S_cls f E)),
        ((nb095_alpha_dummy_673 D R S_cls E), (nb095_alpha_dummy_675 x u D R S_cls f E)),
        ((nb095_alpha_dummy_662 D R S_cls E), (nb095_alpha_dummy_664 x u D R S_cls f E)),
        ((nb095_alpha_dummy_661 D R S_cls E), (nb095_alpha_dummy_663 x u D R S_cls f E)),
        ((nb095_alpha_dummy_667 D R S_cls E), (nb095_alpha_dummy_668 x u D R S_cls f E)),
        ((nb095_alpha_dummy_665 D R S_cls E), (nb095_alpha_dummy_666 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_669 D R S_cls E) ≠ (nb095_alpha_dummy_678 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0730
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_670 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_680 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_680;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0732
                    x u D R S_cls f
                    E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_669 D R S_cls E) ≠
        (nb095_alpha_dummy_677 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_677;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0730
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_670 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_679 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0732
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_669 D R S_cls E) ≠
        (nb095_alpha_dummy_707 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_707;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0734
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_670 x u D R S_cls f E) ≠ (nb095_alpha_dummy_708
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_708;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0735
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_669 D R S_cls E) ≠
        (nb095_alpha_dummy_681 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0731
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_670 x u D R S_cls f E) ≠ (nb095_alpha_dummy_682
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0733
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_003
        D R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_669 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0091 x u D R S_cls f E)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_709 D R S_cls E), (nb095_alpha_dummy_710 x u D R S_cls f E)),
        ((nb095_alpha_dummy_678 D R S_cls E), (nb095_alpha_dummy_680 x u D R S_cls f E)),
        ((nb095_alpha_dummy_677 D R S_cls E), (nb095_alpha_dummy_679 x u D R S_cls f E)),
        ((nb095_alpha_dummy_707 D R S_cls E), (nb095_alpha_dummy_708 x u D R S_cls f E)),
        ((nb095_alpha_dummy_681 D R S_cls E), (nb095_alpha_dummy_682 x u D R S_cls f E)),
        ((nb095_alpha_dummy_669 D R S_cls E), (nb095_alpha_dummy_670 x u D R S_cls f E)),
        ((nb095_alpha_dummy_671 D R S_cls E), (nb095_alpha_dummy_672 x u D R S_cls f E)),
        ((nb095_alpha_dummy_674 D R S_cls E), (nb095_alpha_dummy_676 x u D R S_cls f E)),
        ((nb095_alpha_dummy_673 D R S_cls E), (nb095_alpha_dummy_675 x u D R S_cls f E)),
        ((nb095_alpha_dummy_662 D R S_cls E), (nb095_alpha_dummy_664 x u D R S_cls f E)),
        ((nb095_alpha_dummy_661 D R S_cls E), (nb095_alpha_dummy_663 x u D R S_cls f E)),
        ((nb095_alpha_dummy_667 D R S_cls E), (nb095_alpha_dummy_668 x u D R S_cls f E)),
        ((nb095_alpha_dummy_665 D R S_cls E), (nb095_alpha_dummy_666 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_000 D R S_cls E) ≠
                                        (nb095_alpha_dummy_669 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_669;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0748 D R S_cls E) 0))))
                                    (show f ≠ (nb095_alpha_dummy_670 x u D R S_cls f E) from (by
                                        unfold nb095_alpha_dummy_670;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0751 x u D R S_cls f E)
                                                0)))) (TAlphaVar.there (show
                                        (nb095_alpha_dummy_000 D R S_cls E) ≠
        (nb095_alpha_dummy_671 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_671;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0749 D R S_cls E)
                                                  0))))
                                      (show f ≠ (nb095_alpha_dummy_672 x u D R S_cls f E) from
                                        (by
                                          unfold nb095_alpha_dummy_672;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0752 x u D R S_cls f
                                                    E)
                                                  0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_000 D R S_cls E) ≠ (nb095_alpha_dummy_674 D R S_cls E) from (by
          unfold nb095_alpha_dummy_674;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0750 D R S_cls E)
                  1)))) (show f ≠ (nb095_alpha_dummy_676 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_676;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0753 x u D R S_cls
                    f E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_000 D R S_cls E) ≠
        (nb095_alpha_dummy_673 D R S_cls E) from (by
          unfold nb095_alpha_dummy_673;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0750 D R S_cls E)
                  0)))) (show f ≠ (nb095_alpha_dummy_675 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0753 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_000 D R S_cls E) ≠
        (nb095_alpha_dummy_662 D R S_cls E) from (by
          unfold nb095_alpha_dummy_662;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0742 D R S_cls
                    E)
                  1)))) (show f ≠ (nb095_alpha_dummy_664 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_664;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0744 x u D R
                    S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_000 D R S_cls E) ≠
        (nb095_alpha_dummy_661 D R S_cls E) from (by
          unfold nb095_alpha_dummy_661;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0742 D R
                    S_cls E)
                  0)))) (show f ≠ (nb095_alpha_dummy_663 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_663;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0744 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_000 D R S_cls E) ≠
        (nb095_alpha_dummy_667 D R S_cls E) from (by
          unfold nb095_alpha_dummy_667;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0746 D R
                    S_cls E)
                  0)))) (show f ≠ (nb095_alpha_dummy_668 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_668;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0747 x u D
                    R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_000 D R S_cls E) ≠
        (nb095_alpha_dummy_665 D R S_cls E) from (by
          unfold nb095_alpha_dummy_665;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0743 D R
                    S_cls E)
                  0)))) (show f ≠ (nb095_alpha_dummy_666 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_666;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0745 x u
                    D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_000 D R S_cls E) ≠
        (nb095_alpha_dummy_004 D R S_cls E) from (by
          unfold nb095_alpha_dummy_004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0740 D
                    R S_cls E)
                  1)))) (show f ≠ (nb095_alpha_dummy_006 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0741 x
                    u D R S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_000 D R S_cls E) ≠
        (nb095_alpha_dummy_003 D R S_cls E) from (by
          unfold nb095_alpha_dummy_003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0740
                    D R S_cls E)
                  0)))) (show f ≠ (nb095_alpha_dummy_005 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_005;
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
                                      (nb095_alpha_dummy_671 D R S_cls E) ≠
                                        (nb095_alpha_dummy_713 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_713;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0754 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_672 x u D R S_cls f E) ≠
                                        (nb095_alpha_dummy_714 x u D R S_cls f E) from (by
                                        unfold nb095_alpha_dummy_714;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0755 x u D R S_cls f E)
                                                0)))) (TAlphaVar.here _ _ _))))))))))))
              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                            (Class.cv (nb095_alpha_dummy_003 D R S_cls E)))).fv ∪
                        ((syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                            (Class.cv (nb095_alpha_dummy_004 D R S_cls E)))).fv) (by decide))
                    (freshVar_injective (((syn_cfv (Class.cv f)
                            (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)))).fv ∪
                        ((syn_cfv (Class.cv f)
                            (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_662 D R S_cls E) ≠
                                (nb095_alpha_dummy_715 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_715;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0756 D R S_cls E) 0)))) (show
                              (nb095_alpha_dummy_664 x u D R S_cls f E) ≠
                                (nb095_alpha_dummy_717 x u D R S_cls f E) from (by
                                unfold nb095_alpha_dummy_717;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0757 x u D R S_cls f E) 0))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_662 D R S_cls E) ≠
                                  (nb095_alpha_dummy_716 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_716;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0756 D R S_cls E) 1)))) (show
                                (nb095_alpha_dummy_664 x u D R S_cls f E) ≠
                                  (nb095_alpha_dummy_718 x u D R S_cls f E) from (by
                                  unfold nb095_alpha_dummy_718;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0757 x u D R S_cls f E) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_662 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E))).fv)
                              (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                          (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_715 D R S_cls E) ≠ (nb095_alpha_dummy_722 D R S_cls E) from (by
          unfold nb095_alpha_dummy_722;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0760 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_717 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_725 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_725;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0761 x u D R
                    S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_715 D R S_cls E) ≠
        (nb095_alpha_dummy_721 D R S_cls E) from (by
          unfold nb095_alpha_dummy_721;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0760 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_717 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_724 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_724;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0761 x u D
                    R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_715 D R S_cls E) ≠
        (nb095_alpha_dummy_719 D R S_cls E) from (by
          unfold nb095_alpha_dummy_719;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0758 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_717 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_720 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_720;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0759 x u
                    D R S_cls f E)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_723 D R S_cls E), (nb095_alpha_dummy_726 x u D R S_cls f E)),
        ((nb095_alpha_dummy_722 D R S_cls E), (nb095_alpha_dummy_725 x u D R S_cls f E)),
        ((nb095_alpha_dummy_721 D R S_cls E), (nb095_alpha_dummy_724 x u D R S_cls f E)),
        ((nb095_alpha_dummy_719 D R S_cls E), (nb095_alpha_dummy_720 x u D R S_cls f E)),
        ((nb095_alpha_dummy_715 D R S_cls E), (nb095_alpha_dummy_717 x u D R S_cls f E)),
        ((nb095_alpha_dummy_716 D R S_cls E), (nb095_alpha_dummy_718 x u D R S_cls f E)),
        ((nb095_alpha_dummy_662 D R S_cls E), (nb095_alpha_dummy_664 x u D R S_cls f E)),
        ((nb095_alpha_dummy_661 D R S_cls E), (nb095_alpha_dummy_663 x u D R S_cls f E)),
        ((nb095_alpha_dummy_667 D R S_cls E), (nb095_alpha_dummy_668 x u D R S_cls f E)),
        ((nb095_alpha_dummy_665 D R S_cls E), (nb095_alpha_dummy_666 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_722
        D R S_cls E) ≠ (nb095_alpha_dummy_729 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0764
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_725 x u D R S_cls f E) ≠ (nb095_alpha_dummy_730
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_730;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0765
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_722 D R S_cls E) ≠
        (nb095_alpha_dummy_727 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_727;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0762
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_725 x u D R S_cls f E) ≠ (nb095_alpha_dummy_728
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_728;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0763
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_715
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_717 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_723 D R S_cls E) ≠
        (nb095_alpha_dummy_729 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0768
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_726 x u D R S_cls f E) ≠ (nb095_alpha_dummy_730
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_730;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0769
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_723 D R S_cls E) ≠
        (nb095_alpha_dummy_727 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_727;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0766
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_726 x u D R S_cls f E) ≠ (nb095_alpha_dummy_728
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_728;
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
        (TAlphaVar.there (show (nb095_alpha_dummy_722 D R S_cls E) ≠ (nb095_alpha_dummy_729
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0764
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_725 x u D R S_cls f E) ≠ (nb095_alpha_dummy_730
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_730;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0765
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_722 D R S_cls E) ≠
        (nb095_alpha_dummy_727 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_727;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0762
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_725 x u D R S_cls f E) ≠ (nb095_alpha_dummy_728
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_728;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0763
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_715
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_717 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_723 D R S_cls E) ≠
        (nb095_alpha_dummy_729 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0768
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_726 x u D R S_cls f E) ≠ (nb095_alpha_dummy_730
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_730;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0769
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_723 D R S_cls E) ≠
        (nb095_alpha_dummy_727 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_727;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0766
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_726 x u D R S_cls f E) ≠ (nb095_alpha_dummy_728
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_728;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0767
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_723 D R S_cls E), (nb095_alpha_dummy_726 x u D R S_cls f E)),
        ((nb095_alpha_dummy_722 D R S_cls E), (nb095_alpha_dummy_725 x u D R S_cls f E)),
        ((nb095_alpha_dummy_721 D R S_cls E), (nb095_alpha_dummy_724 x u D R S_cls f E)),
        ((nb095_alpha_dummy_719 D R S_cls E), (nb095_alpha_dummy_720 x u D R S_cls f E)),
        ((nb095_alpha_dummy_715 D R S_cls E), (nb095_alpha_dummy_717 x u D R S_cls f E)),
        ((nb095_alpha_dummy_716 D R S_cls E), (nb095_alpha_dummy_718 x u D R S_cls f E)),
        ((nb095_alpha_dummy_662 D R S_cls E), (nb095_alpha_dummy_664 x u D R S_cls f E)),
        ((nb095_alpha_dummy_661 D R S_cls E), (nb095_alpha_dummy_663 x u D R S_cls f E)),
        ((nb095_alpha_dummy_667 D R S_cls E), (nb095_alpha_dummy_668 x u D R S_cls f E)),
        ((nb095_alpha_dummy_665 D R S_cls E), (nb095_alpha_dummy_666 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_715 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_717 x u D R S_cls f E))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_715 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_717 x u D R S_cls f E))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_722
        D R S_cls E) ≠ (nb095_alpha_dummy_733 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_733;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0772
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_725 x u D R S_cls f E) ≠ (nb095_alpha_dummy_734
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_734;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0773
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_722 D R S_cls E) ≠
        (nb095_alpha_dummy_731 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_731;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0770
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_725 x u D R S_cls f E) ≠ (nb095_alpha_dummy_732
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_732;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0771
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_715
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_717 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_722 D R S_cls E) ≠
        (nb095_alpha_dummy_733 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_733;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0772
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_725 x u D R S_cls f E) ≠ (nb095_alpha_dummy_734
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_734;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0773
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_722 D R S_cls E) ≠
        (nb095_alpha_dummy_731 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_731;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0770
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_725 x u D R S_cls f E) ≠ (nb095_alpha_dummy_732
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_732;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0771
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_715
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_717 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_723 D R S_cls E) ≠ (nb095_alpha_dummy_735
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0776
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_726 x u D R S_cls f E) ≠ (nb095_alpha_dummy_736
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0777
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_723 D R S_cls E) ≠
        (nb095_alpha_dummy_731 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_731;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0774
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_726 x u D R S_cls f E) ≠ (nb095_alpha_dummy_732
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_732;
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_723
        D R S_cls E) ≠ (nb095_alpha_dummy_735 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0776
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_726 x u D R S_cls f E) ≠ (nb095_alpha_dummy_736
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0777
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_723 D R S_cls E) ≠
        (nb095_alpha_dummy_731 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_731;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0774
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_726 x u D R S_cls f E) ≠ (nb095_alpha_dummy_732
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_732;
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
                                        (nb095_alpha_dummy_715 D R S_cls E) ≠
        (nb095_alpha_dummy_719 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_719;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0758 D R S_cls E)
                                                  0)))) (show
                                        (nb095_alpha_dummy_717 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_720 x u D R S_cls f E) from (by
                                          unfold nb095_alpha_dummy_720;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0759 x u D R S_cls f
                                                    E)
                                                  0)))) (TAlphaVar.here _ _ _)))
                                  (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_719 D R S_cls E),
                                        (nb095_alpha_dummy_720 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_715 D R S_cls E),
                                        (nb095_alpha_dummy_717 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_716 D R S_cls E),
                                        (nb095_alpha_dummy_718 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_662 D R S_cls E),
                                        (nb095_alpha_dummy_664 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_661 D R S_cls E),
                                        (nb095_alpha_dummy_663 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_667 D R S_cls E),
                                        (nb095_alpha_dummy_668 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_665 D R S_cls E),
                                        (nb095_alpha_dummy_666 x u D R S_cls f E)),
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
                                      (nb095_alpha_dummy_715 D R S_cls E) ≠
                                        (nb095_alpha_dummy_719 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_719;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0758 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_717 x u D R S_cls f E) ≠
                                        (nb095_alpha_dummy_720 x u D R S_cls f E) from (by
                                        unfold nb095_alpha_dummy_720;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0759 x u D R S_cls f E)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_715 D R S_cls E) ≠
        (nb095_alpha_dummy_719 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_719;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0758 D R S_cls E)
                                                  0)))) (show
                                        (nb095_alpha_dummy_717 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_720 x u D R S_cls f E) from (by
                                          unfold nb095_alpha_dummy_720;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0759 x u D R S_cls f
                                                    E)
                                                  0)))) (TAlphaVar.here _ _ _)))
                                  (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_719 D R S_cls E),
                                        (nb095_alpha_dummy_720 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_715 D R S_cls E),
                                        (nb095_alpha_dummy_717 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_716 D R S_cls E),
                                        (nb095_alpha_dummy_718 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_662 D R S_cls E),
                                        (nb095_alpha_dummy_664 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_661 D R S_cls E),
                                        (nb095_alpha_dummy_663 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_667 D R S_cls E),
                                        (nb095_alpha_dummy_668 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_665 D R S_cls E),
                                        (nb095_alpha_dummy_666 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_004 D R S_cls E),
                                        (nb095_alpha_dummy_006 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_003 D R S_cls E),
                                        (nb095_alpha_dummy_005 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_001 D R S_cls E), u),
                                      ((nb095_alpha_dummy_002 D R S_cls E), x),
                                      ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
