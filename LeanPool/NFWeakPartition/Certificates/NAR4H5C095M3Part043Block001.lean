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

@[expose]
noncomputable def nb095_split_alpha_0095 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_f_u : f ≠ u) (dv_f_x : f ≠ x) :
    TAlphaWff
      [((nb095_alpha_dummy_662 D R S_cls E), (nb095_alpha_dummy_664 x u D R S_cls f E)),
        ((nb095_alpha_dummy_661 D R S_cls E), (nb095_alpha_dummy_663 x u D R S_cls f E)),
        ((nb095_alpha_dummy_737 D R S_cls E), (nb095_alpha_dummy_738 x u D R S_cls f E)),
        ((nb095_alpha_dummy_665 D R S_cls E), (nb095_alpha_dummy_666 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_662 D R S_cls E))
          (syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_004 D R S_cls E)))) (Wff.neg
          (Wff.classEq (Class.cv (nb095_alpha_dummy_661 D R S_cls E))
            (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E)))
              (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E))
          (syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)))) (Wff.neg
          (Wff.classEq (Class.cv (nb095_alpha_dummy_663 x u D R S_cls f E))
            (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E)))
              (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there (freshVar_injective
                  (((Class.cab (nb095_alpha_dummy_741 D R S_cls E) (Wff.classEq
                        (Class.cab (nb095_alpha_dummy_739 D R S_cls E)
                          (syn_wbr (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
                            (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                            (Class.cv (nb095_alpha_dummy_739 D R S_cls E))))
                        (syn_csn (Class.cv (nb095_alpha_dummy_741 D R S_cls E)))))).fv)
                  (by decide)) (freshVar_injective
                  (((Class.cab (nb095_alpha_dummy_742 x u D R S_cls f E) (Wff.classEq
                        (Class.cab (nb095_alpha_dummy_740 x u D R S_cls f E)
                          (syn_wbr (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))
                            (Class.cv f) (Class.cv (nb095_alpha_dummy_740 x u D R S_cls f E))))
                        (syn_csn (Class.cv (nb095_alpha_dummy_742 x u D R S_cls f E)))))).fv)
                  (by decide)) (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.classMem (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                    (nb095_split_alpha_0093 x u D R S_cls f E)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_739 D R S_cls E) ≠
        (nb095_alpha_dummy_748 D R S_cls E) from (by
          unfold nb095_alpha_dummy_748;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0818 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_740 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_750 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_750;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0820 x u
                    D R S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_739 D R S_cls E) ≠
        (nb095_alpha_dummy_747 D R S_cls E) from (by
          unfold nb095_alpha_dummy_747;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0818 D
                    R S_cls E)
                  0)))) (show (nb095_alpha_dummy_740 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_749 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_749;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0820 x
                    u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_739 D R S_cls E) ≠
        (nb095_alpha_dummy_777 D R S_cls E) from (by
          unfold nb095_alpha_dummy_777;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0822
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_740 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_778 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_778;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0823
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_739 D R S_cls E) ≠
        (nb095_alpha_dummy_751 D R S_cls E) from (by
          unfold nb095_alpha_dummy_751;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0819
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_740 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_752 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_752;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0821
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_004 D R S_cls
        E))).fv ∪ ((Class.cv (nb095_alpha_dummy_739 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_740 x u D R S_cls f E))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0094 x u D R S_cls f E)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_779 D R S_cls E), (nb095_alpha_dummy_780 x u D R S_cls f E)),
        ((nb095_alpha_dummy_748 D R S_cls E), (nb095_alpha_dummy_750 x u D R S_cls f E)),
        ((nb095_alpha_dummy_747 D R S_cls E), (nb095_alpha_dummy_749 x u D R S_cls f E)),
        ((nb095_alpha_dummy_777 D R S_cls E), (nb095_alpha_dummy_778 x u D R S_cls f E)),
        ((nb095_alpha_dummy_751 D R S_cls E), (nb095_alpha_dummy_752 x u D R S_cls f E)),
        ((nb095_alpha_dummy_739 D R S_cls E), (nb095_alpha_dummy_740 x u D R S_cls f E)),
        ((nb095_alpha_dummy_741 D R S_cls E), (nb095_alpha_dummy_742 x u D R S_cls f E)),
        ((nb095_alpha_dummy_744 D R S_cls E), (nb095_alpha_dummy_746 x u D R S_cls f E)),
        ((nb095_alpha_dummy_743 D R S_cls E), (nb095_alpha_dummy_745 x u D R S_cls f E)),
        ((nb095_alpha_dummy_662 D R S_cls E), (nb095_alpha_dummy_664 x u D R S_cls f E)),
        ((nb095_alpha_dummy_661 D R S_cls E), (nb095_alpha_dummy_663 x u D R S_cls f E)),
        ((nb095_alpha_dummy_737 D R S_cls E), (nb095_alpha_dummy_738 x u D R S_cls f E)),
        ((nb095_alpha_dummy_665 D R S_cls E), (nb095_alpha_dummy_666 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_739 D R S_cls E) ≠
        (nb095_alpha_dummy_748 D R S_cls E) from (by
          unfold nb095_alpha_dummy_748;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0818 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_740 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_750 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_750;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0820 x u
                    D R S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_739 D R S_cls E) ≠
        (nb095_alpha_dummy_747 D R S_cls E) from (by
          unfold nb095_alpha_dummy_747;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0818 D
                    R S_cls E)
                  0)))) (show (nb095_alpha_dummy_740 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_749 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_749;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0820 x
                    u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_739 D R S_cls E) ≠
        (nb095_alpha_dummy_777 D R S_cls E) from (by
          unfold nb095_alpha_dummy_777;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0822
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_740 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_778 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_778;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0823
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_739 D R S_cls E) ≠
        (nb095_alpha_dummy_751 D R S_cls E) from (by
          unfold nb095_alpha_dummy_751;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0819
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_740 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_752 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_752;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0821
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_004 D R S_cls
        E))).fv ∪ ((Class.cv (nb095_alpha_dummy_739 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_740 x u D R S_cls f E))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0094 x u D R S_cls f E)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_779 D R S_cls E), (nb095_alpha_dummy_780 x u D R S_cls f E)),
        ((nb095_alpha_dummy_748 D R S_cls E), (nb095_alpha_dummy_750 x u D R S_cls f E)),
        ((nb095_alpha_dummy_747 D R S_cls E), (nb095_alpha_dummy_749 x u D R S_cls f E)),
        ((nb095_alpha_dummy_777 D R S_cls E), (nb095_alpha_dummy_778 x u D R S_cls f E)),
        ((nb095_alpha_dummy_751 D R S_cls E), (nb095_alpha_dummy_752 x u D R S_cls f E)),
        ((nb095_alpha_dummy_739 D R S_cls E), (nb095_alpha_dummy_740 x u D R S_cls f E)),
        ((nb095_alpha_dummy_741 D R S_cls E), (nb095_alpha_dummy_742 x u D R S_cls f E)),
        ((nb095_alpha_dummy_744 D R S_cls E), (nb095_alpha_dummy_746 x u D R S_cls f E)),
        ((nb095_alpha_dummy_743 D R S_cls E), (nb095_alpha_dummy_745 x u D R S_cls f E)),
        ((nb095_alpha_dummy_662 D R S_cls E), (nb095_alpha_dummy_664 x u D R S_cls f E)),
        ((nb095_alpha_dummy_661 D R S_cls E), (nb095_alpha_dummy_663 x u D R S_cls f E)),
        ((nb095_alpha_dummy_737 D R S_cls E), (nb095_alpha_dummy_738 x u D R S_cls f E)),
        ((nb095_alpha_dummy_665 D R S_cls E), (nb095_alpha_dummy_666 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
                            (nb095_alpha_dummy_000 D R S_cls E) ≠
                              (nb095_alpha_dummy_739 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_739;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0830 D R S_cls E)
                                      0))))
                          (show f ≠ (nb095_alpha_dummy_740 x u D R S_cls f E) from (by
                              unfold nb095_alpha_dummy_740;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb095_support_mem_0833 x u D R S_cls f E) 0))))
                          (TAlphaVar.there (show (nb095_alpha_dummy_000 D R S_cls E) ≠
                                (nb095_alpha_dummy_741 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_741;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0831 D R S_cls E) 0))))
                            (show f ≠ (nb095_alpha_dummy_742 x u D R S_cls f E) from (by
                                unfold nb095_alpha_dummy_742;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0834 x u D R S_cls f E) 0))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_000 D R S_cls E) ≠
                                  (nb095_alpha_dummy_744 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_744;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0832 D R S_cls E) 1))))
                              (show f ≠ (nb095_alpha_dummy_746 x u D R S_cls f E) from (by
                                  unfold nb095_alpha_dummy_746;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0835 x u D R S_cls f E) 1))))
                              (TAlphaVar.there (show (nb095_alpha_dummy_000 D R S_cls E) ≠
                                    (nb095_alpha_dummy_743 D R S_cls E) from (by
                                    unfold nb095_alpha_dummy_743;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0832 D R S_cls E) 0))))
                                (show f ≠ (nb095_alpha_dummy_745 x u D R S_cls f E) from (by
                                    unfold nb095_alpha_dummy_745;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0835 x u D R S_cls f E)
                                            0)))) (TAlphaVar.there (show
                                    (nb095_alpha_dummy_000 D R S_cls E) ≠
                                      (nb095_alpha_dummy_662 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_662;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0742 D R S_cls E) 1))))
                                  (show f ≠ (nb095_alpha_dummy_664 x u D R S_cls f E) from (by
                                      unfold nb095_alpha_dummy_664;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0744 x u D R S_cls f E)
                                              1)))) (TAlphaVar.there (show
                                      (nb095_alpha_dummy_000 D R S_cls E) ≠
                                        (nb095_alpha_dummy_661 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_661;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0742 D R S_cls E) 0))))
                                    (show f ≠ (nb095_alpha_dummy_663 x u D R S_cls f E) from (by
                                        unfold nb095_alpha_dummy_663;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0744 x u D R S_cls f E)
                                                0)))) (TAlphaVar.there (show
                                        (nb095_alpha_dummy_000 D R S_cls E) ≠
        (nb095_alpha_dummy_737 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_737;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0828 D R S_cls E)
                                                  0))))
                                      (show f ≠ (nb095_alpha_dummy_738 x u D R S_cls f E) from
                                        (by
                                          unfold nb095_alpha_dummy_738;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0829 x u D R S_cls f
                                                    E)
                                                  0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_000 D R S_cls E) ≠ (nb095_alpha_dummy_665 D R S_cls E) from (by
          unfold nb095_alpha_dummy_665;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0743 D R S_cls E)
                  0)))) (show f ≠ (nb095_alpha_dummy_666 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_666;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0745 x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_000 D R S_cls E) ≠
        (nb095_alpha_dummy_004 D R S_cls E) from (by
          unfold nb095_alpha_dummy_004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0740 D R S_cls E)
                  1)))) (show f ≠ (nb095_alpha_dummy_006 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0741 x u D R
                    S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_000 D R S_cls E) ≠
        (nb095_alpha_dummy_003 D R S_cls E) from (by
          unfold nb095_alpha_dummy_003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0740 D R S_cls
                    E)
                  0)))) (show f ≠ (nb095_alpha_dummy_005 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_005;
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
                        (TAlphaVar.there (show (nb095_alpha_dummy_741 D R S_cls E) ≠
                              (nb095_alpha_dummy_783 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_783;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0836 D R S_cls E)
                                      0)))) (show (nb095_alpha_dummy_742 x u D R S_cls f E) ≠
                              (nb095_alpha_dummy_784 x u D R S_cls f E) from (by
                              unfold nb095_alpha_dummy_784;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb095_support_mem_0837 x u D R S_cls f E) 0))))
                          (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                    (Class.cv (nb095_alpha_dummy_003 D R S_cls E)))).fv ∪
                ((syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                    (Class.cv (nb095_alpha_dummy_004 D R S_cls E)))).fv) (by decide))
            (freshVar_injective (((syn_cfv (Class.cv f)
                    (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)))).fv ∪
                ((syn_cfv (Class.cv f)
                    (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
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
                                                (nb095_support_mem_0757 x u D R S_cls f E)
                                                0)))) (TAlphaVar.there (show
                                        (nb095_alpha_dummy_662 D R S_cls E) ≠
        (nb095_alpha_dummy_716 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_716;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0756 D R S_cls E)
                                                  1)))) (show
                                        (nb095_alpha_dummy_664 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_718 x u D R S_cls f E) from (by
                                          unfold nb095_alpha_dummy_718;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0757 x u D R S_cls f
                                                    E)
                                                  1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_662 D R S_cls E) ≠ (nb095_alpha_dummy_787 D R S_cls E) from (by
          unfold nb095_alpha_dummy_787;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0840 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_664 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_788 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_788;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0841 x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_662 D R S_cls E) ≠
        (nb095_alpha_dummy_785 D R S_cls E) from (by
          unfold nb095_alpha_dummy_785;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0838 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_664 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_786 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_786;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0839 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                  (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_662 D R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_664 x u D R S_cls f E))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_715 D R S_cls E) ≠
        (nb095_alpha_dummy_722 D R S_cls E) from (by
          unfold nb095_alpha_dummy_722;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0760
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_717 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_725 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_725;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0761
                    x u D R S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_715 D R S_cls E) ≠
        (nb095_alpha_dummy_721 D R S_cls E) from (by
          unfold nb095_alpha_dummy_721;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0760
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_717 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_724 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_724;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0761
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_715 D R S_cls E) ≠
        (nb095_alpha_dummy_719 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_719;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0758
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_717 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_720 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_720;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0759
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_723 D R S_cls E), (nb095_alpha_dummy_726 x u D R S_cls f E)),
        ((nb095_alpha_dummy_722 D R S_cls E), (nb095_alpha_dummy_725 x u D R S_cls f E)),
        ((nb095_alpha_dummy_721 D R S_cls E), (nb095_alpha_dummy_724 x u D R S_cls f E)),
        ((nb095_alpha_dummy_719 D R S_cls E), (nb095_alpha_dummy_720 x u D R S_cls f E)),
        ((nb095_alpha_dummy_715 D R S_cls E), (nb095_alpha_dummy_717 x u D R S_cls f E)),
        ((nb095_alpha_dummy_716 D R S_cls E), (nb095_alpha_dummy_718 x u D R S_cls f E)),
        ((nb095_alpha_dummy_787 D R S_cls E), (nb095_alpha_dummy_788 x u D R S_cls f E)),
        ((nb095_alpha_dummy_785 D R S_cls E), (nb095_alpha_dummy_786 x u D R S_cls f E)),
        ((nb095_alpha_dummy_662 D R S_cls E), (nb095_alpha_dummy_664 x u D R S_cls f E)),
        ((nb095_alpha_dummy_661 D R S_cls E), (nb095_alpha_dummy_663 x u D R S_cls f E)),
        ((nb095_alpha_dummy_737 D R S_cls E), (nb095_alpha_dummy_738 x u D R S_cls f E)),
        ((nb095_alpha_dummy_665 D R S_cls E), (nb095_alpha_dummy_666 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_722 D R S_cls E) ≠
        (nb095_alpha_dummy_729 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0764
                    D
                    R
                    S_cls
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
                    x
                    u
                    D
                    R
                    S_cls
                    f
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
                    D
                    R
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
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_715
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_717 x u D R S_cls f
        E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_723
        D R S_cls E) ≠ (nb095_alpha_dummy_729 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0768
                    D
                    R
                    S_cls
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
                    x
                    u
                    D
                    R
                    S_cls
                    f
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
                    D
                    R
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
        (TAlphaVar.there (show (nb095_alpha_dummy_722 D R S_cls E) ≠ (nb095_alpha_dummy_729 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0764
                    D
                    R
                    S_cls
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
                    x
                    u
                    D
                    R
                    S_cls
                    f
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
                    D
                    R
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
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_715
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_717 x u D R S_cls f
        E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_723
        D R S_cls E) ≠ (nb095_alpha_dummy_729 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0768
                    D
                    R
                    S_cls
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
                    x
                    u
                    D
                    R
                    S_cls
                    f
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
                    D
                    R
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
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_723 D R S_cls E), (nb095_alpha_dummy_726 x u D R S_cls f E)),
        ((nb095_alpha_dummy_722 D R S_cls E), (nb095_alpha_dummy_725 x u D R S_cls f E)),
        ((nb095_alpha_dummy_721 D R S_cls E), (nb095_alpha_dummy_724 x u D R S_cls f E)),
        ((nb095_alpha_dummy_719 D R S_cls E), (nb095_alpha_dummy_720 x u D R S_cls f E)),
        ((nb095_alpha_dummy_715 D R S_cls E), (nb095_alpha_dummy_717 x u D R S_cls f E)),
        ((nb095_alpha_dummy_716 D R S_cls E), (nb095_alpha_dummy_718 x u D R S_cls f E)),
        ((nb095_alpha_dummy_787 D R S_cls E), (nb095_alpha_dummy_788 x u D R S_cls f E)),
        ((nb095_alpha_dummy_785 D R S_cls E), (nb095_alpha_dummy_786 x u D R S_cls f E)),
        ((nb095_alpha_dummy_662 D R S_cls E), (nb095_alpha_dummy_664 x u D R S_cls f E)),
        ((nb095_alpha_dummy_661 D R S_cls E), (nb095_alpha_dummy_663 x u D R S_cls f E)),
        ((nb095_alpha_dummy_737 D R S_cls E), (nb095_alpha_dummy_738 x u D R S_cls f E)),
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
                    D
                    R
                    S_cls
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
                    x
                    u
                    D
                    R
                    S_cls
                    f
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
                    D
                    R
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
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_715
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_717 x u D R S_cls f
        E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_722
        D R S_cls E) ≠ (nb095_alpha_dummy_733 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_733;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0772
                    D
                    R
                    S_cls
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
                    x
                    u
                    D
                    R
                    S_cls
                    f
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
                    D
                    R
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
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_715
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_717 x u D R S_cls f
        E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_723 D R S_cls E) ≠ (nb095_alpha_dummy_735 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0776
                    D
                    R
                    S_cls
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
                    x
                    u
                    D
                    R
                    S_cls
                    f
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
                    D
                    R
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
                    x
                    u
                    D
                    R
                    S_cls
                    f
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
                    D
                    R
                    S_cls
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
                    x
                    u
                    D
                    R
                    S_cls
                    f
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
                    D
                    R
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
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_715 D R S_cls E) ≠
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
                  (nb095_support_mem_0759 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_719 D R S_cls E), (nb095_alpha_dummy_720 x u D R S_cls f E)),
        ((nb095_alpha_dummy_715 D R S_cls E), (nb095_alpha_dummy_717 x u D R S_cls f E)),
        ((nb095_alpha_dummy_716 D R S_cls E), (nb095_alpha_dummy_718 x u D R S_cls f E)),
        ((nb095_alpha_dummy_787 D R S_cls E), (nb095_alpha_dummy_788 x u D R S_cls f E)),
        ((nb095_alpha_dummy_785 D R S_cls E), (nb095_alpha_dummy_786 x u D R S_cls f E)),
        ((nb095_alpha_dummy_662 D R S_cls E), (nb095_alpha_dummy_664 x u D R S_cls f E)),
        ((nb095_alpha_dummy_661 D R S_cls E), (nb095_alpha_dummy_663 x u D R S_cls f E)),
        ((nb095_alpha_dummy_737 D R S_cls E), (nb095_alpha_dummy_738 x u D R S_cls f E)),
        ((nb095_alpha_dummy_665 D R S_cls E), (nb095_alpha_dummy_666 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_715 D R S_cls E) ≠
        (nb095_alpha_dummy_719 D R S_cls E) from (by
          unfold nb095_alpha_dummy_719;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0758 D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_717 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_720 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_720;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0759 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_715 D R S_cls E) ≠
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
                  (nb095_support_mem_0759 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_719 D R S_cls E), (nb095_alpha_dummy_720 x u D R S_cls f E)),
        ((nb095_alpha_dummy_715 D R S_cls E), (nb095_alpha_dummy_717 x u D R S_cls f E)),
        ((nb095_alpha_dummy_716 D R S_cls E), (nb095_alpha_dummy_718 x u D R S_cls f E)),
        ((nb095_alpha_dummy_787 D R S_cls E), (nb095_alpha_dummy_788 x u D R S_cls f E)),
        ((nb095_alpha_dummy_785 D R S_cls E), (nb095_alpha_dummy_786 x u D R S_cls f E)),
        ((nb095_alpha_dummy_662 D R S_cls E), (nb095_alpha_dummy_664 x u D R S_cls f E)),
        ((nb095_alpha_dummy_661 D R S_cls E), (nb095_alpha_dummy_663 x u D R S_cls f E)),
        ((nb095_alpha_dummy_737 D R S_cls E), (nb095_alpha_dummy_738 x u D R S_cls f E)),
        ((nb095_alpha_dummy_665 D R S_cls E), (nb095_alpha_dummy_666 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
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
                                                (nb095_support_mem_0757 x u D R S_cls f E)
                                                0)))) (TAlphaVar.there (show
                                        (nb095_alpha_dummy_662 D R S_cls E) ≠
        (nb095_alpha_dummy_716 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_716;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0756 D R S_cls E)
                                                  1)))) (show
                                        (nb095_alpha_dummy_664 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_718 x u D R S_cls f E) from (by
                                          unfold nb095_alpha_dummy_718;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0757 x u D R S_cls f
                                                    E)
                                                  1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_662 D R S_cls E) ≠ (nb095_alpha_dummy_787 D R S_cls E) from (by
          unfold nb095_alpha_dummy_787;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0840 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_664 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_788 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_788;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0841 x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_662 D R S_cls E) ≠
        (nb095_alpha_dummy_785 D R S_cls E) from (by
          unfold nb095_alpha_dummy_785;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0838 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_664 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_786 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_786;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0839 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                  (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_662 D R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_664 x u D R S_cls f E))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_715 D R S_cls E) ≠
        (nb095_alpha_dummy_722 D R S_cls E) from (by
          unfold nb095_alpha_dummy_722;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0760
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_717 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_725 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_725;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0761
                    x u D R S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_715 D R S_cls E) ≠
        (nb095_alpha_dummy_721 D R S_cls E) from (by
          unfold nb095_alpha_dummy_721;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0760
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_717 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_724 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_724;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0761
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_715 D R S_cls E) ≠
        (nb095_alpha_dummy_719 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_719;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0758
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_717 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_720 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_720;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0759
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_723 D R S_cls E), (nb095_alpha_dummy_726 x u D R S_cls f E)),
        ((nb095_alpha_dummy_722 D R S_cls E), (nb095_alpha_dummy_725 x u D R S_cls f E)),
        ((nb095_alpha_dummy_721 D R S_cls E), (nb095_alpha_dummy_724 x u D R S_cls f E)),
        ((nb095_alpha_dummy_719 D R S_cls E), (nb095_alpha_dummy_720 x u D R S_cls f E)),
        ((nb095_alpha_dummy_715 D R S_cls E), (nb095_alpha_dummy_717 x u D R S_cls f E)),
        ((nb095_alpha_dummy_716 D R S_cls E), (nb095_alpha_dummy_718 x u D R S_cls f E)),
        ((nb095_alpha_dummy_787 D R S_cls E), (nb095_alpha_dummy_788 x u D R S_cls f E)),
        ((nb095_alpha_dummy_785 D R S_cls E), (nb095_alpha_dummy_786 x u D R S_cls f E)),
        ((nb095_alpha_dummy_662 D R S_cls E), (nb095_alpha_dummy_664 x u D R S_cls f E)),
        ((nb095_alpha_dummy_661 D R S_cls E), (nb095_alpha_dummy_663 x u D R S_cls f E)),
        ((nb095_alpha_dummy_737 D R S_cls E), (nb095_alpha_dummy_738 x u D R S_cls f E)),
        ((nb095_alpha_dummy_665 D R S_cls E), (nb095_alpha_dummy_666 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_722 D R S_cls E) ≠
        (nb095_alpha_dummy_729 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0764
                    D
                    R
                    S_cls
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
                    x
                    u
                    D
                    R
                    S_cls
                    f
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
                    D
                    R
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
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_715
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_717 x u D R S_cls f
        E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_723
        D R S_cls E) ≠ (nb095_alpha_dummy_729 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0768
                    D
                    R
                    S_cls
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
                    x
                    u
                    D
                    R
                    S_cls
                    f
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
                    D
                    R
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
        (TAlphaVar.there (show (nb095_alpha_dummy_722 D R S_cls E) ≠ (nb095_alpha_dummy_729 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0764
                    D
                    R
                    S_cls
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
                    x
                    u
                    D
                    R
                    S_cls
                    f
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
                    D
                    R
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
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_715
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_717 x u D R S_cls f
        E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_723
        D R S_cls E) ≠ (nb095_alpha_dummy_729 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0768
                    D
                    R
                    S_cls
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
                    x
                    u
                    D
                    R
                    S_cls
                    f
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
                    D
                    R
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
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_723 D R S_cls E), (nb095_alpha_dummy_726 x u D R S_cls f E)),
        ((nb095_alpha_dummy_722 D R S_cls E), (nb095_alpha_dummy_725 x u D R S_cls f E)),
        ((nb095_alpha_dummy_721 D R S_cls E), (nb095_alpha_dummy_724 x u D R S_cls f E)),
        ((nb095_alpha_dummy_719 D R S_cls E), (nb095_alpha_dummy_720 x u D R S_cls f E)),
        ((nb095_alpha_dummy_715 D R S_cls E), (nb095_alpha_dummy_717 x u D R S_cls f E)),
        ((nb095_alpha_dummy_716 D R S_cls E), (nb095_alpha_dummy_718 x u D R S_cls f E)),
        ((nb095_alpha_dummy_787 D R S_cls E), (nb095_alpha_dummy_788 x u D R S_cls f E)),
        ((nb095_alpha_dummy_785 D R S_cls E), (nb095_alpha_dummy_786 x u D R S_cls f E)),
        ((nb095_alpha_dummy_662 D R S_cls E), (nb095_alpha_dummy_664 x u D R S_cls f E)),
        ((nb095_alpha_dummy_661 D R S_cls E), (nb095_alpha_dummy_663 x u D R S_cls f E)),
        ((nb095_alpha_dummy_737 D R S_cls E), (nb095_alpha_dummy_738 x u D R S_cls f E)),
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
                    D
                    R
                    S_cls
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
                    x
                    u
                    D
                    R
                    S_cls
                    f
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
                    D
                    R
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
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_715
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_717 x u D R S_cls f
        E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_722
        D R S_cls E) ≠ (nb095_alpha_dummy_733 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_733;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0772
                    D
                    R
                    S_cls
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
                    x
                    u
                    D
                    R
                    S_cls
                    f
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
                    D
                    R
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
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_715
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_717 x u D R S_cls f
        E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_723 D R S_cls E) ≠ (nb095_alpha_dummy_735 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0776
                    D
                    R
                    S_cls
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
                    x
                    u
                    D
                    R
                    S_cls
                    f
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
                    D
                    R
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
                    x
                    u
                    D
                    R
                    S_cls
                    f
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
                    D
                    R
                    S_cls
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
                    x
                    u
                    D
                    R
                    S_cls
                    f
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
                    D
                    R
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
                    x
                    u
                    D
                    R
                    S_cls
                    f
                    E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_715 D R S_cls E) ≠
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
                  (nb095_support_mem_0759 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_719 D R S_cls E), (nb095_alpha_dummy_720 x u D R S_cls f E)),
        ((nb095_alpha_dummy_715 D R S_cls E), (nb095_alpha_dummy_717 x u D R S_cls f E)),
        ((nb095_alpha_dummy_716 D R S_cls E), (nb095_alpha_dummy_718 x u D R S_cls f E)),
        ((nb095_alpha_dummy_787 D R S_cls E), (nb095_alpha_dummy_788 x u D R S_cls f E)),
        ((nb095_alpha_dummy_785 D R S_cls E), (nb095_alpha_dummy_786 x u D R S_cls f E)),
        ((nb095_alpha_dummy_662 D R S_cls E), (nb095_alpha_dummy_664 x u D R S_cls f E)),
        ((nb095_alpha_dummy_661 D R S_cls E), (nb095_alpha_dummy_663 x u D R S_cls f E)),
        ((nb095_alpha_dummy_737 D R S_cls E), (nb095_alpha_dummy_738 x u D R S_cls f E)),
        ((nb095_alpha_dummy_665 D R S_cls E), (nb095_alpha_dummy_666 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_715 D R S_cls E) ≠
        (nb095_alpha_dummy_719 D R S_cls E) from (by
          unfold nb095_alpha_dummy_719;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0758 D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_717 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_720 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_720;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0759 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_715 D R S_cls E) ≠
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
                  (nb095_support_mem_0759 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_719 D R S_cls E), (nb095_alpha_dummy_720 x u D R S_cls f E)),
        ((nb095_alpha_dummy_715 D R S_cls E), (nb095_alpha_dummy_717 x u D R S_cls f E)),
        ((nb095_alpha_dummy_716 D R S_cls E), (nb095_alpha_dummy_718 x u D R S_cls f E)),
        ((nb095_alpha_dummy_787 D R S_cls E), (nb095_alpha_dummy_788 x u D R S_cls f E)),
        ((nb095_alpha_dummy_785 D R S_cls E), (nb095_alpha_dummy_786 x u D R S_cls f E)),
        ((nb095_alpha_dummy_662 D R S_cls E), (nb095_alpha_dummy_664 x u D R S_cls f E)),
        ((nb095_alpha_dummy_661 D R S_cls E), (nb095_alpha_dummy_663 x u D R S_cls f E)),
        ((nb095_alpha_dummy_737 D R S_cls E), (nb095_alpha_dummy_738 x u D R S_cls f E)),
        ((nb095_alpha_dummy_665 D R S_cls E), (nb095_alpha_dummy_666 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_785 D R S_cls E),
                      (nb095_alpha_dummy_786 x u D R S_cls f E)),
                    ((nb095_alpha_dummy_662 D R S_cls E),
                      (nb095_alpha_dummy_664 x u D R S_cls f E)),
                    ((nb095_alpha_dummy_661 D R S_cls E),
                      (nb095_alpha_dummy_663 x u D R S_cls f E)),
                    ((nb095_alpha_dummy_737 D R S_cls E),
                      (nb095_alpha_dummy_738 x u D R S_cls f E)),
                    ((nb095_alpha_dummy_665 D R S_cls E),
                      (nb095_alpha_dummy_666 x u D R S_cls f E)),
                    ((nb095_alpha_dummy_004 D R S_cls E),
                      (nb095_alpha_dummy_006 x u D R S_cls f E)),
                    ((nb095_alpha_dummy_003 D R S_cls E),
                      (nb095_alpha_dummy_005 x u D R S_cls f E)),
                    ((nb095_alpha_dummy_001 D R S_cls E), u),
                    ((nb095_alpha_dummy_002 D R S_cls E), x),
                    ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_ccompl (syn_csn (syn_c0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

theorem nb095_focused_notmem_0072 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_791 D R S_cls E) ∉ S_cls.fv :=
  by
  change
    freshVar
        ((S_cls).fv ∪ ((syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))))).fv)
        0 ∉
      S_cls.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (hu))

theorem nb095_focused_notmem_0073 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_792 u S_cls E) ∉ S_cls.fv :=
  by
  change
    freshVar
        ((S_cls).fv ∪ ((syn_cxp (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv u)))))).fv)
        0 ∉
      S_cls.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (hu))

theorem nb095_focused_notmem_0074 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_789 D R S_cls E) ∉ S_cls.fv :=
  by
  change
    freshVar
        (((syn_cnin S_cls (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                    (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                    (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))))).fv ∪
          ((syn_cnin S_cls (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                    (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                    (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))))).fv)
        0 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin S_cls
      (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0075 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_790 u S_cls E) ∉ S_cls.fv :=
  by
  change
    freshVar
        (((syn_cnin S_cls (syn_cxp (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                    (syn_csn (Class.cv u))))))).fv ∪ ((syn_cnin S_cls (syn_cxp (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                    (syn_csn (Class.cv u))))))).fv)
        0 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin S_cls
      (syn_cxp (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0076 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_004 D R S_cls E) ∉ S_cls.fv :=
  by
  change
    freshVar
        (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪ ((syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                          (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                            (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))))).fv ∪
              ((syn_cin S_cls (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                        (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                        (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))))).fv ∪
            ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv ∪ ((syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv)
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
      (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0077 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    (nb095_alpha_dummy_006 x u D R S_cls f E) ∉ S_cls.fv :=
  by
  change
    freshVar
        (((Class.cv f)).fv ∪ ((syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))
                      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                          (syn_csn (Class.cv x))))))).fv ∪ ((syn_cin S_cls (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))
                    (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                        (syn_csn (Class.cv u))))))).fv ∪ ((syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv ∪
          ((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv u))))).fv)
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
      (syn_cxp (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0078 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_003 D R S_cls E) ∉ S_cls.fv :=
  by
  change
    freshVar
        (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪ ((syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                          (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                            (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))))).fv ∪
              ((syn_cin S_cls (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                        (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                        (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))))).fv ∪
            ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv ∪ ((syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv)
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
      (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0079 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    (nb095_alpha_dummy_005 x u D R S_cls f E) ∉ S_cls.fv :=
  by
  change
    freshVar
        (((Class.cv f)).fv ∪ ((syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))
                      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                          (syn_csn (Class.cv x))))))).fv ∪ ((syn_cin S_cls (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))
                    (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                        (syn_csn (Class.cv u))))))).fv ∪ ((syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv ∪
          ((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv u))))).fv)
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
      (syn_cxp (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_compact_envfresh_0328 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_S_f : f ∉ S_cls.fv) (dv_S_u : u ∉ S_cls.fv)
    (dv_S_x : x ∉ S_cls.fv) :
    TEnvFresh
      [((nb095_alpha_dummy_791 D R S_cls E), (nb095_alpha_dummy_792 u S_cls E)),
        ((nb095_alpha_dummy_789 D R S_cls E), (nb095_alpha_dummy_790 u S_cls E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      S_cls.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb095_alpha_dummy_791 D R S_cls E)
      (nb095_alpha_dummy_792 u S_cls E) (nb095_focused_notmem_0072 D R S_cls E)
      (nb095_focused_notmem_0073 u S_cls E)
      (TEnvFresh.consFresh (nb095_alpha_dummy_789 D R S_cls E)
        (nb095_alpha_dummy_790 u S_cls E) (nb095_focused_notmem_0074 D R S_cls E)
        (nb095_focused_notmem_0075 u S_cls E)
        (TEnvFresh.consFresh (nb095_alpha_dummy_004 D R S_cls E)
          (nb095_alpha_dummy_006 x u D R S_cls f E) (nb095_focused_notmem_0076 D R S_cls E)
          (nb095_focused_notmem_0077 x u D R S_cls f E)
          (TEnvFresh.consFresh (nb095_alpha_dummy_003 D R S_cls E)
            (nb095_alpha_dummy_005 x u D R S_cls f E) (nb095_focused_notmem_0078 D R S_cls E)
            (nb095_focused_notmem_0079 x u D R S_cls f E)
            (TEnvFresh.consFresh (nb095_alpha_dummy_001 D R S_cls E) u
              (nb095_focused_notmem_0041 D R S_cls E) dv_S_u
              (TEnvFresh.consFresh (nb095_alpha_dummy_002 D R S_cls E) x
                (nb095_focused_notmem_0042 D R S_cls E) dv_S_x
                (TEnvFresh.consFresh (nb095_alpha_dummy_000 D R S_cls E) f
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

@[expose]
noncomputable def nb095_focused_refl_0009 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_S_f : f ∉ S_cls.fv) (dv_S_u : u ∉ S_cls.fv)
    (dv_S_x : x ∉ S_cls.fv) :
    TReflOn
      [((nb095_alpha_dummy_791 D R S_cls E), (nb095_alpha_dummy_792 u S_cls E)),
        ((nb095_alpha_dummy_789 D R S_cls E), (nb095_alpha_dummy_790 u S_cls E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      S_cls.fv :=
  TEnvFresh.reflOn (nb095_compact_envfresh_0328 x u D R S_cls f E dv_S_f dv_S_u dv_S_x)

theorem nb095_compact_fv_empty_0614 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_794 D R S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0615 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_796 u S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0616 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_793 D R S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0617 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_795 u S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0618 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_797 D R S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0619 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_798 u S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0620 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_791 D R S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0621 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_792 u S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0622 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_789 D R S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0623 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_790 u S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
