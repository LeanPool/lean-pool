/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block039

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part120`. -/


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
noncomputable def nb078_split_alpha_0096 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_759), (nb078_alpha_dummy_760 g)),
        ((nb078_alpha_dummy_728), (nb078_alpha_dummy_730 g)),
        ((nb078_alpha_dummy_727), (nb078_alpha_dummy_729 g)),
        ((nb078_alpha_dummy_757), (nb078_alpha_dummy_758 g)),
        ((nb078_alpha_dummy_731), (nb078_alpha_dummy_732 g)),
        ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
        ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb078_alpha_dummy_759))
            (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_728)))))
          (Wff.classMem (Class.cv (nb078_alpha_dummy_759)) (syn_ccompl (syn_csn (syn_c0c))))))
      (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb078_alpha_dummy_760 g))
            (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_730 g)))))
          (Wff.classMem (Class.cv (nb078_alpha_dummy_760 g))
            (syn_ccompl (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_728) ≠ (nb078_alpha_dummy_735) from (by
                                unfold nb078_alpha_dummy_735;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0766) 0))))
                            (show (nb078_alpha_dummy_730 g) ≠ (nb078_alpha_dummy_737 g) from (by
                                unfold nb078_alpha_dummy_737;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0767 g) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_728) ≠ (nb078_alpha_dummy_736) from (by
                                  unfold nb078_alpha_dummy_736;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0766) 1))))
                              (show (nb078_alpha_dummy_730 g) ≠ (nb078_alpha_dummy_738 g) from
                                (by
                                  unfold nb078_alpha_dummy_738;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0767 g) 1))))
                              (TAlphaVar.there
                                (show (nb078_alpha_dummy_728) ≠ (nb078_alpha_dummy_761) from (by
                                    unfold nb078_alpha_dummy_761;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0796) 0)))) (show
                                  (nb078_alpha_dummy_730 g) ≠ (nb078_alpha_dummy_762 g) from (by
                                    unfold nb078_alpha_dummy_762;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0797 g)
                                            0)))) (TAlphaVar.there
                                  (show (nb078_alpha_dummy_728) ≠ (nb078_alpha_dummy_759) from
                                    (by
                                      unfold nb078_alpha_dummy_759;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0794)
                                              0)))) (show
                                    (nb078_alpha_dummy_730 g) ≠ (nb078_alpha_dummy_760 g) from
                                    (by
                                      unfold nb078_alpha_dummy_760;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0795 g)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_728))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_730 g))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_735) ≠ (nb078_alpha_dummy_742) from (by
          unfold nb078_alpha_dummy_742;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0770) 1)))) (show (nb078_alpha_dummy_737 g) ≠
        (nb078_alpha_dummy_745 g) from (by
          unfold nb078_alpha_dummy_745;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0771 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_735) ≠ (nb078_alpha_dummy_741) from (by
          unfold nb078_alpha_dummy_741;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0770) 0)))) (show (nb078_alpha_dummy_737 g) ≠
        (nb078_alpha_dummy_744 g) from (by
          unfold nb078_alpha_dummy_744;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0771 g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_735) ≠ (nb078_alpha_dummy_739)
        from (by
          unfold nb078_alpha_dummy_739;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0768)
                  0)))) (show (nb078_alpha_dummy_737 g) ≠ (nb078_alpha_dummy_740 g) from (by
          unfold nb078_alpha_dummy_740;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0769 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_743), (nb078_alpha_dummy_746 g)), ((nb078_alpha_dummy_742),
        (nb078_alpha_dummy_745 g)), ((nb078_alpha_dummy_741), (nb078_alpha_dummy_744 g)),
        ((nb078_alpha_dummy_739), (nb078_alpha_dummy_740 g)), ((nb078_alpha_dummy_735),
        (nb078_alpha_dummy_737 g)), ((nb078_alpha_dummy_736), (nb078_alpha_dummy_738 g)),
        ((nb078_alpha_dummy_761), (nb078_alpha_dummy_762 g)), ((nb078_alpha_dummy_759),
        (nb078_alpha_dummy_760 g)), ((nb078_alpha_dummy_728), (nb078_alpha_dummy_730 g)),
        ((nb078_alpha_dummy_727), (nb078_alpha_dummy_729 g)), ((nb078_alpha_dummy_757),
        (nb078_alpha_dummy_758 g)), ((nb078_alpha_dummy_731), (nb078_alpha_dummy_732 g)),
        ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570),
        (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
        ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_742) ≠ (nb078_alpha_dummy_749) from (by
          unfold
            nb078_alpha_dummy_749;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0774)
                  0)))) (show (nb078_alpha_dummy_745 g) ≠ (nb078_alpha_dummy_750 g) from (by
          unfold
            nb078_alpha_dummy_750;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0775
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_742) ≠ (nb078_alpha_dummy_747)
        from (by
          unfold
            nb078_alpha_dummy_747;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0772)
                  0)))) (show (nb078_alpha_dummy_745 g) ≠ (nb078_alpha_dummy_748 g) from (by
          unfold
            nb078_alpha_dummy_748;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0773
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_743) ≠ (nb078_alpha_dummy_749)
        from (by
          unfold
            nb078_alpha_dummy_749;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0778)
                  0)))) (show (nb078_alpha_dummy_746 g) ≠ (nb078_alpha_dummy_750 g) from (by
          unfold
            nb078_alpha_dummy_750;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0779
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_743) ≠ (nb078_alpha_dummy_747)
        from (by
          unfold
            nb078_alpha_dummy_747;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0776)
                  0)))) (show (nb078_alpha_dummy_746 g) ≠ (nb078_alpha_dummy_748 g) from (by
          unfold
            nb078_alpha_dummy_748;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0777
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_742) ≠ (nb078_alpha_dummy_749) from (by
          unfold
            nb078_alpha_dummy_749;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0774)
                  0)))) (show (nb078_alpha_dummy_745 g) ≠ (nb078_alpha_dummy_750 g) from (by
          unfold
            nb078_alpha_dummy_750;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0775
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_742) ≠ (nb078_alpha_dummy_747)
        from (by
          unfold
            nb078_alpha_dummy_747;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0772)
                  0)))) (show (nb078_alpha_dummy_745 g) ≠ (nb078_alpha_dummy_748 g) from (by
          unfold
            nb078_alpha_dummy_748;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0773
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_743) ≠ (nb078_alpha_dummy_749)
        from (by
          unfold
            nb078_alpha_dummy_749;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0778)
                  0)))) (show (nb078_alpha_dummy_746 g) ≠ (nb078_alpha_dummy_750 g) from (by
          unfold
            nb078_alpha_dummy_750;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0779
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_743) ≠ (nb078_alpha_dummy_747)
        from (by
          unfold
            nb078_alpha_dummy_747;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0776)
                  0)))) (show (nb078_alpha_dummy_746 g) ≠ (nb078_alpha_dummy_748 g) from (by
          unfold
            nb078_alpha_dummy_748;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0777
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_743), (nb078_alpha_dummy_746 g)), ((nb078_alpha_dummy_742),
        (nb078_alpha_dummy_745 g)), ((nb078_alpha_dummy_741), (nb078_alpha_dummy_744 g)),
        ((nb078_alpha_dummy_739), (nb078_alpha_dummy_740 g)), ((nb078_alpha_dummy_735),
        (nb078_alpha_dummy_737 g)), ((nb078_alpha_dummy_736), (nb078_alpha_dummy_738 g)),
        ((nb078_alpha_dummy_761), (nb078_alpha_dummy_762 g)), ((nb078_alpha_dummy_759),
        (nb078_alpha_dummy_760 g)), ((nb078_alpha_dummy_728), (nb078_alpha_dummy_730 g)),
        ((nb078_alpha_dummy_727), (nb078_alpha_dummy_729 g)), ((nb078_alpha_dummy_757),
        (nb078_alpha_dummy_758 g)), ((nb078_alpha_dummy_731), (nb078_alpha_dummy_732 g)),
        ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570),
        (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
        ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_735))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_737
        g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_742) ≠
        (nb078_alpha_dummy_753) from (by
          unfold
            nb078_alpha_dummy_753;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0782)
                  0)))) (show (nb078_alpha_dummy_745 g) ≠ (nb078_alpha_dummy_754 g) from (by
          unfold
            nb078_alpha_dummy_754;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0783
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_742) ≠ (nb078_alpha_dummy_751)
        from (by
          unfold
            nb078_alpha_dummy_751;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0780)
                  0)))) (show (nb078_alpha_dummy_745 g) ≠ (nb078_alpha_dummy_752 g) from (by
          unfold
            nb078_alpha_dummy_752;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0781
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_742) ≠ (nb078_alpha_dummy_753)
        from (by
          unfold
            nb078_alpha_dummy_753;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0782)
                  0)))) (show (nb078_alpha_dummy_745 g) ≠ (nb078_alpha_dummy_754 g) from (by
          unfold
            nb078_alpha_dummy_754;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0783
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_742) ≠ (nb078_alpha_dummy_751)
        from (by
          unfold
            nb078_alpha_dummy_751;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0780)
                  0)))) (show (nb078_alpha_dummy_745 g) ≠ (nb078_alpha_dummy_752 g) from (by
          unfold
            nb078_alpha_dummy_752;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0781
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_743) ≠ (nb078_alpha_dummy_755) from (by
          unfold
            nb078_alpha_dummy_755;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0786)
                  0)))) (show (nb078_alpha_dummy_746 g) ≠ (nb078_alpha_dummy_756 g) from (by
          unfold
            nb078_alpha_dummy_756;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0787
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_743) ≠ (nb078_alpha_dummy_751)
        from (by
          unfold
            nb078_alpha_dummy_751;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0784)
                  0)))) (show (nb078_alpha_dummy_746 g) ≠ (nb078_alpha_dummy_752 g) from (by
          unfold
            nb078_alpha_dummy_752;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0785
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_743) ≠
        (nb078_alpha_dummy_755) from (by
          unfold
            nb078_alpha_dummy_755;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0786)
                  0)))) (show (nb078_alpha_dummy_746 g) ≠ (nb078_alpha_dummy_756 g) from (by
          unfold
            nb078_alpha_dummy_756;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0787
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_743) ≠ (nb078_alpha_dummy_751)
        from (by
          unfold
            nb078_alpha_dummy_751;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0784)
                  0)))) (show (nb078_alpha_dummy_746 g) ≠ (nb078_alpha_dummy_752 g) from (by
          unfold
            nb078_alpha_dummy_752;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0785
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_735) ≠ (nb078_alpha_dummy_739) from
                                        (by
                                          unfold nb078_alpha_dummy_739;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0768)
                                                  0)))) (show (nb078_alpha_dummy_737 g) ≠
        (nb078_alpha_dummy_740 g) from (by
                                          unfold nb078_alpha_dummy_740;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0769 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_739), (nb078_alpha_dummy_740 g)),
                                      ((nb078_alpha_dummy_735), (nb078_alpha_dummy_737 g)),
                                      ((nb078_alpha_dummy_736), (nb078_alpha_dummy_738 g)),
                                      ((nb078_alpha_dummy_761), (nb078_alpha_dummy_762 g)),
                                      ((nb078_alpha_dummy_759), (nb078_alpha_dummy_760 g)),
                                      ((nb078_alpha_dummy_728), (nb078_alpha_dummy_730 g)),
                                      ((nb078_alpha_dummy_727), (nb078_alpha_dummy_729 g)),
                                      ((nb078_alpha_dummy_757), (nb078_alpha_dummy_758 g)),
                                      ((nb078_alpha_dummy_731), (nb078_alpha_dummy_732 g)),
                                      ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                                      ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                                      ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                                      ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                                      ((nb078_alpha_dummy_001), g),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_735) ≠ (nb078_alpha_dummy_739) from (by
                                        unfold nb078_alpha_dummy_739;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0768)
                                                0)))) (show (nb078_alpha_dummy_737 g) ≠
                                        (nb078_alpha_dummy_740 g) from (by
                                        unfold nb078_alpha_dummy_740;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0769 g)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_735) ≠ (nb078_alpha_dummy_739) from
                                        (by
                                          unfold nb078_alpha_dummy_739;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0768)
                                                  0)))) (show (nb078_alpha_dummy_737 g) ≠
        (nb078_alpha_dummy_740 g) from (by
                                          unfold nb078_alpha_dummy_740;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0769 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_739), (nb078_alpha_dummy_740 g)),
                                      ((nb078_alpha_dummy_735), (nb078_alpha_dummy_737 g)),
                                      ((nb078_alpha_dummy_736), (nb078_alpha_dummy_738 g)),
                                      ((nb078_alpha_dummy_761), (nb078_alpha_dummy_762 g)),
                                      ((nb078_alpha_dummy_759), (nb078_alpha_dummy_760 g)),
                                      ((nb078_alpha_dummy_728), (nb078_alpha_dummy_730 g)),
                                      ((nb078_alpha_dummy_727), (nb078_alpha_dummy_729 g)),
                                      ((nb078_alpha_dummy_757), (nb078_alpha_dummy_758 g)),
                                      ((nb078_alpha_dummy_731), (nb078_alpha_dummy_732 g)),
                                      ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                                      ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                                      ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                                      ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                                      ((nb078_alpha_dummy_001), g),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_728) ≠ (nb078_alpha_dummy_735) from (by
                                unfold nb078_alpha_dummy_735;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0766) 0))))
                            (show (nb078_alpha_dummy_730 g) ≠ (nb078_alpha_dummy_737 g) from (by
                                unfold nb078_alpha_dummy_737;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0767 g) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_728) ≠ (nb078_alpha_dummy_736) from (by
                                  unfold nb078_alpha_dummy_736;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0766) 1))))
                              (show (nb078_alpha_dummy_730 g) ≠ (nb078_alpha_dummy_738 g) from
                                (by
                                  unfold nb078_alpha_dummy_738;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0767 g) 1))))
                              (TAlphaVar.there
                                (show (nb078_alpha_dummy_728) ≠ (nb078_alpha_dummy_761) from (by
                                    unfold nb078_alpha_dummy_761;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0796) 0)))) (show
                                  (nb078_alpha_dummy_730 g) ≠ (nb078_alpha_dummy_762 g) from (by
                                    unfold nb078_alpha_dummy_762;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0797 g)
                                            0)))) (TAlphaVar.there
                                  (show (nb078_alpha_dummy_728) ≠ (nb078_alpha_dummy_759) from
                                    (by
                                      unfold nb078_alpha_dummy_759;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0794)
                                              0)))) (show
                                    (nb078_alpha_dummy_730 g) ≠ (nb078_alpha_dummy_760 g) from
                                    (by
                                      unfold nb078_alpha_dummy_760;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0795 g)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_728))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_730 g))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_735) ≠ (nb078_alpha_dummy_742) from (by
          unfold nb078_alpha_dummy_742;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0770) 1)))) (show (nb078_alpha_dummy_737 g) ≠
        (nb078_alpha_dummy_745 g) from (by
          unfold nb078_alpha_dummy_745;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0771 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_735) ≠ (nb078_alpha_dummy_741) from (by
          unfold nb078_alpha_dummy_741;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0770) 0)))) (show (nb078_alpha_dummy_737 g) ≠
        (nb078_alpha_dummy_744 g) from (by
          unfold nb078_alpha_dummy_744;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0771 g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_735) ≠ (nb078_alpha_dummy_739)
        from (by
          unfold nb078_alpha_dummy_739;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0768)
                  0)))) (show (nb078_alpha_dummy_737 g) ≠ (nb078_alpha_dummy_740 g) from (by
          unfold nb078_alpha_dummy_740;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0769 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_743), (nb078_alpha_dummy_746 g)), ((nb078_alpha_dummy_742),
        (nb078_alpha_dummy_745 g)), ((nb078_alpha_dummy_741), (nb078_alpha_dummy_744 g)),
        ((nb078_alpha_dummy_739), (nb078_alpha_dummy_740 g)), ((nb078_alpha_dummy_735),
        (nb078_alpha_dummy_737 g)), ((nb078_alpha_dummy_736), (nb078_alpha_dummy_738 g)),
        ((nb078_alpha_dummy_761), (nb078_alpha_dummy_762 g)), ((nb078_alpha_dummy_759),
        (nb078_alpha_dummy_760 g)), ((nb078_alpha_dummy_728), (nb078_alpha_dummy_730 g)),
        ((nb078_alpha_dummy_727), (nb078_alpha_dummy_729 g)), ((nb078_alpha_dummy_757),
        (nb078_alpha_dummy_758 g)), ((nb078_alpha_dummy_731), (nb078_alpha_dummy_732 g)),
        ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570),
        (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
        ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_742) ≠ (nb078_alpha_dummy_749) from (by
          unfold
            nb078_alpha_dummy_749;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0774)
                  0)))) (show (nb078_alpha_dummy_745 g) ≠ (nb078_alpha_dummy_750 g) from (by
          unfold
            nb078_alpha_dummy_750;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0775
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_742) ≠ (nb078_alpha_dummy_747)
        from (by
          unfold
            nb078_alpha_dummy_747;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0772)
                  0)))) (show (nb078_alpha_dummy_745 g) ≠ (nb078_alpha_dummy_748 g) from (by
          unfold
            nb078_alpha_dummy_748;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0773
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_743) ≠ (nb078_alpha_dummy_749)
        from (by
          unfold
            nb078_alpha_dummy_749;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0778)
                  0)))) (show (nb078_alpha_dummy_746 g) ≠ (nb078_alpha_dummy_750 g) from (by
          unfold
            nb078_alpha_dummy_750;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0779
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_743) ≠ (nb078_alpha_dummy_747)
        from (by
          unfold
            nb078_alpha_dummy_747;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0776)
                  0)))) (show (nb078_alpha_dummy_746 g) ≠ (nb078_alpha_dummy_748 g) from (by
          unfold
            nb078_alpha_dummy_748;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0777
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_742) ≠ (nb078_alpha_dummy_749) from (by
          unfold
            nb078_alpha_dummy_749;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0774)
                  0)))) (show (nb078_alpha_dummy_745 g) ≠ (nb078_alpha_dummy_750 g) from (by
          unfold
            nb078_alpha_dummy_750;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0775
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_742) ≠ (nb078_alpha_dummy_747)
        from (by
          unfold
            nb078_alpha_dummy_747;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0772)
                  0)))) (show (nb078_alpha_dummy_745 g) ≠ (nb078_alpha_dummy_748 g) from (by
          unfold
            nb078_alpha_dummy_748;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0773
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_743) ≠ (nb078_alpha_dummy_749)
        from (by
          unfold
            nb078_alpha_dummy_749;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0778)
                  0)))) (show (nb078_alpha_dummy_746 g) ≠ (nb078_alpha_dummy_750 g) from (by
          unfold
            nb078_alpha_dummy_750;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0779
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_743) ≠ (nb078_alpha_dummy_747)
        from (by
          unfold
            nb078_alpha_dummy_747;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0776)
                  0)))) (show (nb078_alpha_dummy_746 g) ≠ (nb078_alpha_dummy_748 g) from (by
          unfold
            nb078_alpha_dummy_748;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0777
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_743), (nb078_alpha_dummy_746 g)), ((nb078_alpha_dummy_742),
        (nb078_alpha_dummy_745 g)), ((nb078_alpha_dummy_741), (nb078_alpha_dummy_744 g)),
        ((nb078_alpha_dummy_739), (nb078_alpha_dummy_740 g)), ((nb078_alpha_dummy_735),
        (nb078_alpha_dummy_737 g)), ((nb078_alpha_dummy_736), (nb078_alpha_dummy_738 g)),
        ((nb078_alpha_dummy_761), (nb078_alpha_dummy_762 g)), ((nb078_alpha_dummy_759),
        (nb078_alpha_dummy_760 g)), ((nb078_alpha_dummy_728), (nb078_alpha_dummy_730 g)),
        ((nb078_alpha_dummy_727), (nb078_alpha_dummy_729 g)), ((nb078_alpha_dummy_757),
        (nb078_alpha_dummy_758 g)), ((nb078_alpha_dummy_731), (nb078_alpha_dummy_732 g)),
        ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570),
        (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
        ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_735))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_737
        g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_742) ≠
        (nb078_alpha_dummy_753) from (by
          unfold
            nb078_alpha_dummy_753;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0782)
                  0)))) (show (nb078_alpha_dummy_745 g) ≠ (nb078_alpha_dummy_754 g) from (by
          unfold
            nb078_alpha_dummy_754;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0783
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_742) ≠ (nb078_alpha_dummy_751)
        from (by
          unfold
            nb078_alpha_dummy_751;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0780)
                  0)))) (show (nb078_alpha_dummy_745 g) ≠ (nb078_alpha_dummy_752 g) from (by
          unfold
            nb078_alpha_dummy_752;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0781
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_742) ≠ (nb078_alpha_dummy_753)
        from (by
          unfold
            nb078_alpha_dummy_753;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0782)
                  0)))) (show (nb078_alpha_dummy_745 g) ≠ (nb078_alpha_dummy_754 g) from (by
          unfold
            nb078_alpha_dummy_754;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0783
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_742) ≠ (nb078_alpha_dummy_751)
        from (by
          unfold
            nb078_alpha_dummy_751;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0780)
                  0)))) (show (nb078_alpha_dummy_745 g) ≠ (nb078_alpha_dummy_752 g) from (by
          unfold
            nb078_alpha_dummy_752;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0781
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_743) ≠ (nb078_alpha_dummy_755) from (by
          unfold
            nb078_alpha_dummy_755;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0786)
                  0)))) (show (nb078_alpha_dummy_746 g) ≠ (nb078_alpha_dummy_756 g) from (by
          unfold
            nb078_alpha_dummy_756;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0787
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_743) ≠ (nb078_alpha_dummy_751)
        from (by
          unfold
            nb078_alpha_dummy_751;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0784)
                  0)))) (show (nb078_alpha_dummy_746 g) ≠ (nb078_alpha_dummy_752 g) from (by
          unfold
            nb078_alpha_dummy_752;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0785
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_743) ≠
        (nb078_alpha_dummy_755) from (by
          unfold
            nb078_alpha_dummy_755;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0786)
                  0)))) (show (nb078_alpha_dummy_746 g) ≠ (nb078_alpha_dummy_756 g) from (by
          unfold
            nb078_alpha_dummy_756;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0787
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_743) ≠ (nb078_alpha_dummy_751)
        from (by
          unfold
            nb078_alpha_dummy_751;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0784)
                  0)))) (show (nb078_alpha_dummy_746 g) ≠ (nb078_alpha_dummy_752 g) from (by
          unfold
            nb078_alpha_dummy_752;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0785
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_735) ≠ (nb078_alpha_dummy_739) from
                                        (by
                                          unfold nb078_alpha_dummy_739;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0768)
                                                  0)))) (show (nb078_alpha_dummy_737 g) ≠
        (nb078_alpha_dummy_740 g) from (by
                                          unfold nb078_alpha_dummy_740;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0769 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_739), (nb078_alpha_dummy_740 g)),
                                      ((nb078_alpha_dummy_735), (nb078_alpha_dummy_737 g)),
                                      ((nb078_alpha_dummy_736), (nb078_alpha_dummy_738 g)),
                                      ((nb078_alpha_dummy_761), (nb078_alpha_dummy_762 g)),
                                      ((nb078_alpha_dummy_759), (nb078_alpha_dummy_760 g)),
                                      ((nb078_alpha_dummy_728), (nb078_alpha_dummy_730 g)),
                                      ((nb078_alpha_dummy_727), (nb078_alpha_dummy_729 g)),
                                      ((nb078_alpha_dummy_757), (nb078_alpha_dummy_758 g)),
                                      ((nb078_alpha_dummy_731), (nb078_alpha_dummy_732 g)),
                                      ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                                      ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                                      ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                                      ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                                      ((nb078_alpha_dummy_001), g),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_735) ≠ (nb078_alpha_dummy_739) from (by
                                        unfold nb078_alpha_dummy_739;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0768)
                                                0)))) (show (nb078_alpha_dummy_737 g) ≠
                                        (nb078_alpha_dummy_740 g) from (by
                                        unfold nb078_alpha_dummy_740;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0769 g)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_735) ≠ (nb078_alpha_dummy_739) from
                                        (by
                                          unfold nb078_alpha_dummy_739;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0768)
                                                  0)))) (show (nb078_alpha_dummy_737 g) ≠
        (nb078_alpha_dummy_740 g) from (by
                                          unfold nb078_alpha_dummy_740;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0769 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_739), (nb078_alpha_dummy_740 g)),
                                      ((nb078_alpha_dummy_735), (nb078_alpha_dummy_737 g)),
                                      ((nb078_alpha_dummy_736), (nb078_alpha_dummy_738 g)),
                                      ((nb078_alpha_dummy_761), (nb078_alpha_dummy_762 g)),
                                      ((nb078_alpha_dummy_759), (nb078_alpha_dummy_760 g)),
                                      ((nb078_alpha_dummy_728), (nb078_alpha_dummy_730 g)),
                                      ((nb078_alpha_dummy_727), (nb078_alpha_dummy_729 g)),
                                      ((nb078_alpha_dummy_757), (nb078_alpha_dummy_758 g)),
                                      ((nb078_alpha_dummy_731), (nb078_alpha_dummy_732 g)),
                                      ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                                      ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                                      ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                                      ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                                      ((nb078_alpha_dummy_001), g),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
          [((nb078_alpha_dummy_759), (nb078_alpha_dummy_760 g)),
            ((nb078_alpha_dummy_728), (nb078_alpha_dummy_730 g)),
            ((nb078_alpha_dummy_727), (nb078_alpha_dummy_729 g)),
            ((nb078_alpha_dummy_757), (nb078_alpha_dummy_758 g)),
            ((nb078_alpha_dummy_731), (nb078_alpha_dummy_732 g)),
            ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
            ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
            ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
            ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
            ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
            ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part121`. -/


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
noncomputable def nb078_split_alpha_0097 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_379), (nb078_alpha_dummy_380 g)),
        ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)),
        ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
        ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
        ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)),
        ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
        ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_379))
          (Class.cab (nb078_alpha_dummy_373)
            (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_367))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_373))
                (syn_cphi (Class.cv (nb078_alpha_dummy_374))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_379)) (Class.cab (nb078_alpha_dummy_373)
              (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_367))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_373))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_374)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_380 g))
          (Class.cab (nb078_alpha_dummy_375 g)
            (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_369 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_376 g))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_380 g))
            (Class.cab (nb078_alpha_dummy_375 g)
              (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_369 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_376 g))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_374) from
                    (by
                      unfold nb078_alpha_dummy_374;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0374) 1))))
                  (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_376 g) from (by
                      unfold nb078_alpha_dummy_376;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0376 g) 1))))
                  (TAlphaVar.there (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_373) from
                      (by
                        unfold nb078_alpha_dummy_373;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0374) 0))))
                    (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_375 g) from (by
                        unfold nb078_alpha_dummy_375;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0376 g) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_379) from (by
                          unfold nb078_alpha_dummy_379;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0378) 0))))
                      (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_380 g) from (by
                          unfold nb078_alpha_dummy_380;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0379 g) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_377) from (by
                            unfold nb078_alpha_dummy_377;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0375) 0))))
                        (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_378 g) from (by
                            unfold nb078_alpha_dummy_378;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0377 g) 0))))
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_001))).fv)
                            (by decide)) (freshVar_injective (((Class.cv g)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_367))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_368))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078_alpha_dummy_369 g))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_370 g))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_374) ≠ (nb078_alpha_dummy_381) from (by
                              unfold nb078_alpha_dummy_381;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0380) 0))))
                          (show (nb078_alpha_dummy_376 g) ≠ (nb078_alpha_dummy_383 g) from (by
                              unfold nb078_alpha_dummy_383;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0381 g) 0))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_374) ≠ (nb078_alpha_dummy_382) from (by
                                unfold nb078_alpha_dummy_382;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0380) 1))))
                            (show (nb078_alpha_dummy_376 g) ≠ (nb078_alpha_dummy_384 g) from (by
                                unfold nb078_alpha_dummy_384;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0381 g) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_374))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_376 g))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_388) from (by
          unfold nb078_alpha_dummy_388;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0384) 1)))) (show (nb078_alpha_dummy_383 g) ≠
        (nb078_alpha_dummy_391 g) from (by
          unfold nb078_alpha_dummy_391;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0385 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_387) from (by
          unfold nb078_alpha_dummy_387;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0384) 0)))) (show (nb078_alpha_dummy_383 g) ≠
        (nb078_alpha_dummy_390 g) from (by
          unfold nb078_alpha_dummy_390;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0385 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_385) from (by
          unfold nb078_alpha_dummy_385;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0382) 0)))) (show (nb078_alpha_dummy_383 g) ≠
        (nb078_alpha_dummy_386 g) from (by
          unfold nb078_alpha_dummy_386;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0383 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_389), (nb078_alpha_dummy_392 g)), ((nb078_alpha_dummy_388),
        (nb078_alpha_dummy_391 g)), ((nb078_alpha_dummy_387), (nb078_alpha_dummy_390 g)),
        ((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)), ((nb078_alpha_dummy_381),
        (nb078_alpha_dummy_383 g)), ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)),
        ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)), ((nb078_alpha_dummy_373),
        (nb078_alpha_dummy_375 g)), ((nb078_alpha_dummy_379), (nb078_alpha_dummy_380 g)),
        ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)), ((nb078_alpha_dummy_368),
        (nb078_alpha_dummy_370 g)), ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
        ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_571),
        (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575),
        (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_395) from (by
          unfold
            nb078_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0388)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_396 g) from (by
          unfold
            nb078_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0389
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_393)
        from (by
          unfold
            nb078_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0386)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_394 g) from (by
          unfold
            nb078_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0387
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_395)
        from (by
          unfold
            nb078_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0392)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_396 g) from (by
          unfold
            nb078_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0393
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_393)
        from (by
          unfold
            nb078_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0390)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_394 g) from (by
          unfold
            nb078_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0391
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_395) from (by
          unfold
            nb078_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0388)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_396 g) from (by
          unfold
            nb078_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0389
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_393)
        from (by
          unfold
            nb078_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0386)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_394 g) from (by
          unfold
            nb078_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0387
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_395)
        from (by
          unfold
            nb078_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0392)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_396 g) from (by
          unfold
            nb078_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0393
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_393)
        from (by
          unfold
            nb078_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0390)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_394 g) from (by
          unfold
            nb078_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0391
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_389), (nb078_alpha_dummy_392 g)), ((nb078_alpha_dummy_388),
        (nb078_alpha_dummy_391 g)), ((nb078_alpha_dummy_387), (nb078_alpha_dummy_390 g)),
        ((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)), ((nb078_alpha_dummy_381),
        (nb078_alpha_dummy_383 g)), ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)),
        ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)), ((nb078_alpha_dummy_373),
        (nb078_alpha_dummy_375 g)), ((nb078_alpha_dummy_379), (nb078_alpha_dummy_380 g)),
        ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)), ((nb078_alpha_dummy_368),
        (nb078_alpha_dummy_370 g)), ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
        ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_571),
        (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575),
        (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_381))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_383
        g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_399) from (by
          unfold
            nb078_alpha_dummy_399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0396)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_400 g) from (by
          unfold
            nb078_alpha_dummy_400;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0397
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_397)
        from (by
          unfold
            nb078_alpha_dummy_397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0394)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_398 g) from (by
          unfold
            nb078_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0395
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_399)
        from (by
          unfold
            nb078_alpha_dummy_399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0396)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_400 g) from (by
          unfold
            nb078_alpha_dummy_400;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0397
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_397)
        from (by
          unfold
            nb078_alpha_dummy_397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0394)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_398 g) from (by
          unfold
            nb078_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0395
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_401) from (by
          unfold
            nb078_alpha_dummy_401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0400)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_402 g) from (by
          unfold
            nb078_alpha_dummy_402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0401
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_397)
        from (by
          unfold
            nb078_alpha_dummy_397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0398)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_398 g) from (by
          unfold
            nb078_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0399
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠
        (nb078_alpha_dummy_401) from (by
          unfold
            nb078_alpha_dummy_401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0400)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_402 g) from (by
          unfold
            nb078_alpha_dummy_402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0401
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_397)
        from (by
          unfold
            nb078_alpha_dummy_397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0398)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_398 g) from (by
          unfold
            nb078_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0399
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_385) from (by
                                        unfold nb078_alpha_dummy_385;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0382)
                                                0)))) (show (nb078_alpha_dummy_383 g) ≠
                                        (nb078_alpha_dummy_386 g) from (by
                                        unfold nb078_alpha_dummy_386;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0383 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)),
                                    ((nb078_alpha_dummy_381), (nb078_alpha_dummy_383 g)),
                                    ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)),
                                    ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)),
                                    ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)),
                                    ((nb078_alpha_dummy_379), (nb078_alpha_dummy_380 g)),
                                    ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)),
                                    ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
                                    ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
                                    ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)),
                                    ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                                    ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                                    ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                                    ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                                    ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_385) from
                                    (by
                                      unfold nb078_alpha_dummy_385;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0382)
                                              0)))) (show
                                    (nb078_alpha_dummy_383 g) ≠ (nb078_alpha_dummy_386 g) from
                                    (by
                                      unfold nb078_alpha_dummy_386;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0383 g)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_385) from (by
                                        unfold nb078_alpha_dummy_385;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0382)
                                                0)))) (show (nb078_alpha_dummy_383 g) ≠
                                        (nb078_alpha_dummy_386 g) from (by
                                        unfold nb078_alpha_dummy_386;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0383 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)),
                                    ((nb078_alpha_dummy_381), (nb078_alpha_dummy_383 g)),
                                    ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)),
                                    ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)),
                                    ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)),
                                    ((nb078_alpha_dummy_379), (nb078_alpha_dummy_380 g)),
                                    ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)),
                                    ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
                                    ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
                                    ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)),
                                    ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                                    ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                                    ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                                    ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                                    ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_374) from
                      (by
                        unfold nb078_alpha_dummy_374;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0374) 1))))
                    (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_376 g) from (by
                        unfold nb078_alpha_dummy_376;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0376 g) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_373) from (by
                          unfold nb078_alpha_dummy_373;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0374) 0))))
                      (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_375 g) from (by
                          unfold nb078_alpha_dummy_375;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0376 g) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_379) from (by
                            unfold nb078_alpha_dummy_379;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0378) 0))))
                        (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_380 g) from (by
                            unfold nb078_alpha_dummy_380;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0379 g) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_377) from (by
                              unfold nb078_alpha_dummy_377;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0375) 0))))
                          (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_378 g) from (by
                              unfold nb078_alpha_dummy_378;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0377 g) 0))))
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_001))).fv)
                              (by decide)) (freshVar_injective (((Class.cv g)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078_alpha_dummy_367))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_368))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_369 g))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_370 g))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_374) ≠ (nb078_alpha_dummy_381) from (by
                                unfold nb078_alpha_dummy_381;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0380) 0))))
                            (show (nb078_alpha_dummy_376 g) ≠ (nb078_alpha_dummy_383 g) from (by
                                unfold nb078_alpha_dummy_383;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0381 g) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_374) ≠ (nb078_alpha_dummy_382) from (by
                                  unfold nb078_alpha_dummy_382;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0380) 1))))
                              (show (nb078_alpha_dummy_376 g) ≠ (nb078_alpha_dummy_384 g) from
                                (by
                                  unfold nb078_alpha_dummy_384;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0381 g) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_374))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_376 g))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_388) from (by
          unfold nb078_alpha_dummy_388;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0384) 1)))) (show (nb078_alpha_dummy_383 g) ≠
        (nb078_alpha_dummy_391 g) from (by
          unfold nb078_alpha_dummy_391;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0385 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_387) from (by
          unfold nb078_alpha_dummy_387;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0384) 0)))) (show (nb078_alpha_dummy_383 g) ≠
        (nb078_alpha_dummy_390 g) from (by
          unfold nb078_alpha_dummy_390;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0385 g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_385)
        from (by
          unfold nb078_alpha_dummy_385;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0382)
                  0)))) (show (nb078_alpha_dummy_383 g) ≠ (nb078_alpha_dummy_386 g) from (by
          unfold nb078_alpha_dummy_386;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0383 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_389), (nb078_alpha_dummy_392 g)), ((nb078_alpha_dummy_388),
        (nb078_alpha_dummy_391 g)), ((nb078_alpha_dummy_387), (nb078_alpha_dummy_390 g)),
        ((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)), ((nb078_alpha_dummy_381),
        (nb078_alpha_dummy_383 g)), ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)),
        ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)), ((nb078_alpha_dummy_373),
        (nb078_alpha_dummy_375 g)), ((nb078_alpha_dummy_379), (nb078_alpha_dummy_380 g)),
        ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)), ((nb078_alpha_dummy_368),
        (nb078_alpha_dummy_370 g)), ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
        ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_571),
        (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575),
        (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_395) from (by
          unfold
            nb078_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0388)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_396 g) from (by
          unfold
            nb078_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0389
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_393)
        from (by
          unfold
            nb078_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0386)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_394 g) from (by
          unfold
            nb078_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0387
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_395)
        from (by
          unfold
            nb078_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0392)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_396 g) from (by
          unfold
            nb078_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0393
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_393)
        from (by
          unfold
            nb078_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0390)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_394 g) from (by
          unfold
            nb078_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0391
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_395) from (by
          unfold
            nb078_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0388)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_396 g) from (by
          unfold
            nb078_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0389
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_393)
        from (by
          unfold
            nb078_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0386)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_394 g) from (by
          unfold
            nb078_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0387
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_395)
        from (by
          unfold
            nb078_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0392)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_396 g) from (by
          unfold
            nb078_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0393
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_393)
        from (by
          unfold
            nb078_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0390)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_394 g) from (by
          unfold
            nb078_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0391
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_389), (nb078_alpha_dummy_392 g)), ((nb078_alpha_dummy_388),
        (nb078_alpha_dummy_391 g)), ((nb078_alpha_dummy_387), (nb078_alpha_dummy_390 g)),
        ((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)), ((nb078_alpha_dummy_381),
        (nb078_alpha_dummy_383 g)), ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)),
        ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)), ((nb078_alpha_dummy_373),
        (nb078_alpha_dummy_375 g)), ((nb078_alpha_dummy_379), (nb078_alpha_dummy_380 g)),
        ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)), ((nb078_alpha_dummy_368),
        (nb078_alpha_dummy_370 g)), ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
        ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_571),
        (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575),
        (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_381))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_383
        g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_399) from (by
          unfold
            nb078_alpha_dummy_399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0396)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_400 g) from (by
          unfold
            nb078_alpha_dummy_400;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0397
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_397)
        from (by
          unfold
            nb078_alpha_dummy_397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0394)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_398 g) from (by
          unfold
            nb078_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0395
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_399)
        from (by
          unfold
            nb078_alpha_dummy_399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0396)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_400 g) from (by
          unfold
            nb078_alpha_dummy_400;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0397
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_397)
        from (by
          unfold
            nb078_alpha_dummy_397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0394)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_398 g) from (by
          unfold
            nb078_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0395
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_401) from (by
          unfold
            nb078_alpha_dummy_401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0400)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_402 g) from (by
          unfold
            nb078_alpha_dummy_402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0401
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_397)
        from (by
          unfold
            nb078_alpha_dummy_397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0398)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_398 g) from (by
          unfold
            nb078_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0399
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠
        (nb078_alpha_dummy_401) from (by
          unfold
            nb078_alpha_dummy_401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0400)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_402 g) from (by
          unfold
            nb078_alpha_dummy_402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0401
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_397)
        from (by
          unfold
            nb078_alpha_dummy_397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0398)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_398 g) from (by
          unfold
            nb078_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0399
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_385) from
                                        (by
                                          unfold nb078_alpha_dummy_385;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0382)
                                                  0)))) (show (nb078_alpha_dummy_383 g) ≠
        (nb078_alpha_dummy_386 g) from (by
                                          unfold nb078_alpha_dummy_386;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0383 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)),
                                      ((nb078_alpha_dummy_381), (nb078_alpha_dummy_383 g)),
                                      ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)),
                                      ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)),
                                      ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)),
                                      ((nb078_alpha_dummy_379), (nb078_alpha_dummy_380 g)),
                                      ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)),
                                      ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
                                      ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
                                      ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)),
                                      ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                                      ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                                      ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                                      ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                                      ((nb078_alpha_dummy_001), g),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_385) from (by
                                        unfold nb078_alpha_dummy_385;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0382)
                                                0)))) (show (nb078_alpha_dummy_383 g) ≠
                                        (nb078_alpha_dummy_386 g) from (by
                                        unfold nb078_alpha_dummy_386;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0383 g)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_385) from
                                        (by
                                          unfold nb078_alpha_dummy_385;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0382)
                                                  0)))) (show (nb078_alpha_dummy_383 g) ≠
        (nb078_alpha_dummy_386 g) from (by
                                          unfold nb078_alpha_dummy_386;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0383 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)),
                                      ((nb078_alpha_dummy_381), (nb078_alpha_dummy_383 g)),
                                      ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)),
                                      ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)),
                                      ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)),
                                      ((nb078_alpha_dummy_379), (nb078_alpha_dummy_380 g)),
                                      ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)),
                                      ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
                                      ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
                                      ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)),
                                      ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                                      ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                                      ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                                      ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                                      ((nb078_alpha_dummy_001), g),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part122`. -/


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
noncomputable def nb078_split_alpha_0098 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_407), (nb078_alpha_dummy_408 g)),
        ((nb078_alpha_dummy_405), (nb078_alpha_dummy_406 g)),
        ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)),
        ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)),
        ((nb078_alpha_dummy_403), (nb078_alpha_dummy_404 g)),
        ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)),
        ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
        ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
        ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)),
        ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
        ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_407))
          (syn_cphi (Class.cv (nb078_alpha_dummy_374)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_407))
            (syn_cphi (Class.cv (nb078_alpha_dummy_374))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_408 g))
          (syn_cphi (Class.cv (nb078_alpha_dummy_376 g)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_408 g))
            (syn_cphi (Class.cv (nb078_alpha_dummy_376 g)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_374) ≠ (nb078_alpha_dummy_381) from
                    (by
                      unfold nb078_alpha_dummy_381;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0380) 0))))
                  (show (nb078_alpha_dummy_376 g) ≠ (nb078_alpha_dummy_383 g) from (by
                      unfold nb078_alpha_dummy_383;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0381 g) 0))))
                  (TAlphaVar.there (show (nb078_alpha_dummy_374) ≠ (nb078_alpha_dummy_382) from
                      (by
                        unfold nb078_alpha_dummy_382;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0380) 1))))
                    (show (nb078_alpha_dummy_376 g) ≠ (nb078_alpha_dummy_384 g) from (by
                        unfold nb078_alpha_dummy_384;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0381 g) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_374) ≠ (nb078_alpha_dummy_407) from (by
                          unfold nb078_alpha_dummy_407;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0410) 0))))
                      (show (nb078_alpha_dummy_376 g) ≠ (nb078_alpha_dummy_408 g) from (by
                          unfold nb078_alpha_dummy_408;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0411 g) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_374) ≠ (nb078_alpha_dummy_405) from (by
                            unfold nb078_alpha_dummy_405;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0408) 0))))
                        (show (nb078_alpha_dummy_376 g) ≠ (nb078_alpha_dummy_406 g) from (by
                            unfold nb078_alpha_dummy_406;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0409 g) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_374))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_376 g))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_388) from (by
                                        unfold nb078_alpha_dummy_388;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0384)
                                                1)))) (show (nb078_alpha_dummy_383 g) ≠
                                        (nb078_alpha_dummy_391 g) from (by
                                        unfold nb078_alpha_dummy_391;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0385 g)
                                                1)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_387) from
                                        (by
                                          unfold nb078_alpha_dummy_387;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0384)
                                                  0)))) (show (nb078_alpha_dummy_383 g) ≠
        (nb078_alpha_dummy_390 g) from (by
                                          unfold nb078_alpha_dummy_390;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0385 g) 0))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_381) ≠
        (nb078_alpha_dummy_385) from (by
          unfold nb078_alpha_dummy_385;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0382) 0)))) (show (nb078_alpha_dummy_383 g) ≠
        (nb078_alpha_dummy_386 g) from (by
          unfold nb078_alpha_dummy_386;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0383 g) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_389),
        (nb078_alpha_dummy_392 g)), ((nb078_alpha_dummy_388), (nb078_alpha_dummy_391 g)),
                                        ((nb078_alpha_dummy_387), (nb078_alpha_dummy_390 g)),
                                        ((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)),
                                        ((nb078_alpha_dummy_381), (nb078_alpha_dummy_383 g)),
                                        ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)),
                                        ((nb078_alpha_dummy_407), (nb078_alpha_dummy_408 g)),
                                        ((nb078_alpha_dummy_405), (nb078_alpha_dummy_406 g)),
                                        ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)),
                                        ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)),
                                        ((nb078_alpha_dummy_403), (nb078_alpha_dummy_404 g)),
                                        ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)),
                                        ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
                                        ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
                                        ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)),
                                        ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                                        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                                        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                                        ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                                        ((nb078_alpha_dummy_001), g),
                                        ((nb078_alpha_dummy_004), y),
                                        ((nb078_alpha_dummy_003), x)]
                                      (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠
        (nb078_alpha_dummy_395) from (by
          unfold
            nb078_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0388)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_396 g) from (by
          unfold
            nb078_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0389
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_393)
        from (by
          unfold
            nb078_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0386)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_394 g) from (by
          unfold
            nb078_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0387
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_395)
        from (by
          unfold
            nb078_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0392)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_396 g) from (by
          unfold
            nb078_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0393
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_393)
        from (by
          unfold
            nb078_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0390)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_394 g) from (by
          unfold
            nb078_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0391
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_395) from (by
          unfold
            nb078_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0388)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_396 g) from (by
          unfold
            nb078_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0389
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_393)
        from (by
          unfold
            nb078_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0386)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_394 g) from (by
          unfold
            nb078_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0387
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_395)
        from (by
          unfold
            nb078_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0392)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_396 g) from (by
          unfold
            nb078_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0393
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_393)
        from (by
          unfold
            nb078_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0390)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_394 g) from (by
          unfold
            nb078_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0391
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb078_alpha_dummy_389), (nb078_alpha_dummy_392 g)),
        ((nb078_alpha_dummy_388), (nb078_alpha_dummy_391 g)), ((nb078_alpha_dummy_387),
        (nb078_alpha_dummy_390 g)), ((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)),
        ((nb078_alpha_dummy_381), (nb078_alpha_dummy_383 g)), ((nb078_alpha_dummy_382),
        (nb078_alpha_dummy_384 g)), ((nb078_alpha_dummy_407), (nb078_alpha_dummy_408 g)),
        ((nb078_alpha_dummy_405), (nb078_alpha_dummy_406 g)), ((nb078_alpha_dummy_374),
        (nb078_alpha_dummy_376 g)), ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)),
        ((nb078_alpha_dummy_403), (nb078_alpha_dummy_404 g)), ((nb078_alpha_dummy_377),
        (nb078_alpha_dummy_378 g)), ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
        ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)), ((nb078_alpha_dummy_371),
        (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569),
        (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠
        (nb078_alpha_dummy_399) from (by
          unfold
            nb078_alpha_dummy_399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0396)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_400 g) from (by
          unfold
            nb078_alpha_dummy_400;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0397
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_397)
        from (by
          unfold
            nb078_alpha_dummy_397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0394)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_398 g) from (by
          unfold
            nb078_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0395
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_399)
        from (by
          unfold
            nb078_alpha_dummy_399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0396)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_400 g) from (by
          unfold
            nb078_alpha_dummy_400;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0397
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_397)
        from (by
          unfold
            nb078_alpha_dummy_397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0394)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_398 g) from (by
          unfold
            nb078_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0395
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_401) from (by
          unfold
            nb078_alpha_dummy_401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0400)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_402 g) from (by
          unfold
            nb078_alpha_dummy_402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0401
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_397)
        from (by
          unfold
            nb078_alpha_dummy_397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0398)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_398 g) from (by
          unfold
            nb078_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0399
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠
        (nb078_alpha_dummy_401) from (by
          unfold
            nb078_alpha_dummy_401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0400)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_402 g) from (by
          unfold
            nb078_alpha_dummy_402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0401
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_397)
        from (by
          unfold
            nb078_alpha_dummy_397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0398)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_398 g) from (by
          unfold
            nb078_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0399
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_385) from (by
                                unfold nb078_alpha_dummy_385;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0382) 0))))
                            (show (nb078_alpha_dummy_383 g) ≠ (nb078_alpha_dummy_386 g) from (by
                                unfold nb078_alpha_dummy_386;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0383 g) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)),
                            ((nb078_alpha_dummy_381), (nb078_alpha_dummy_383 g)),
                            ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)),
                            ((nb078_alpha_dummy_407), (nb078_alpha_dummy_408 g)),
                            ((nb078_alpha_dummy_405), (nb078_alpha_dummy_406 g)),
                            ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)),
                            ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)),
                            ((nb078_alpha_dummy_403), (nb078_alpha_dummy_404 g)),
                            ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)),
                            ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
                            ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
                            ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)),
                            ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                            ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                            ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                            ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                            ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                            ((nb078_alpha_dummy_003), x)]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_385) from (by
                              unfold nb078_alpha_dummy_385;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0382) 0))))
                          (show (nb078_alpha_dummy_383 g) ≠ (nb078_alpha_dummy_386 g) from (by
                              unfold nb078_alpha_dummy_386;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0383 g) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_385) from (by
                                unfold nb078_alpha_dummy_385;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0382) 0))))
                            (show (nb078_alpha_dummy_383 g) ≠ (nb078_alpha_dummy_386 g) from (by
                                unfold nb078_alpha_dummy_386;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0383 g) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)),
                            ((nb078_alpha_dummy_381), (nb078_alpha_dummy_383 g)),
                            ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)),
                            ((nb078_alpha_dummy_407), (nb078_alpha_dummy_408 g)),
                            ((nb078_alpha_dummy_405), (nb078_alpha_dummy_406 g)),
                            ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)),
                            ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)),
                            ((nb078_alpha_dummy_403), (nb078_alpha_dummy_404 g)),
                            ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)),
                            ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
                            ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
                            ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)),
                            ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                            ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                            ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                            ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                            ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                            ((nb078_alpha_dummy_003), x)]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb078_alpha_dummy_374) ≠ (nb078_alpha_dummy_381) from (by
                        unfold nb078_alpha_dummy_381;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0380) 0))))
                    (show (nb078_alpha_dummy_376 g) ≠ (nb078_alpha_dummy_383 g) from (by
                        unfold nb078_alpha_dummy_383;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0381 g) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_374) ≠ (nb078_alpha_dummy_382) from (by
                          unfold nb078_alpha_dummy_382;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0380) 1))))
                      (show (nb078_alpha_dummy_376 g) ≠ (nb078_alpha_dummy_384 g) from (by
                          unfold nb078_alpha_dummy_384;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0381 g) 1))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_374) ≠ (nb078_alpha_dummy_407) from (by
                            unfold nb078_alpha_dummy_407;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0410) 0))))
                        (show (nb078_alpha_dummy_376 g) ≠ (nb078_alpha_dummy_408 g) from (by
                            unfold nb078_alpha_dummy_408;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0411 g) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_374) ≠ (nb078_alpha_dummy_405) from (by
                              unfold nb078_alpha_dummy_405;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0408) 0))))
                          (show (nb078_alpha_dummy_376 g) ≠ (nb078_alpha_dummy_406 g) from (by
                              unfold nb078_alpha_dummy_406;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0409 g) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_374))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_376 g))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_388) from
                                        (by
                                          unfold nb078_alpha_dummy_388;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0384)
                                                  1)))) (show (nb078_alpha_dummy_383 g) ≠
        (nb078_alpha_dummy_391 g) from (by
                                          unfold nb078_alpha_dummy_391;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0385 g) 1))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_381) ≠
        (nb078_alpha_dummy_387) from (by
          unfold nb078_alpha_dummy_387;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0384) 0)))) (show (nb078_alpha_dummy_383 g) ≠
        (nb078_alpha_dummy_390 g) from (by
          unfold nb078_alpha_dummy_390;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0385 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_385) from (by
          unfold nb078_alpha_dummy_385;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0382) 0)))) (show (nb078_alpha_dummy_383 g) ≠
        (nb078_alpha_dummy_386 g) from (by
          unfold nb078_alpha_dummy_386;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0383 g) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_389),
        (nb078_alpha_dummy_392 g)), ((nb078_alpha_dummy_388), (nb078_alpha_dummy_391 g)),
        ((nb078_alpha_dummy_387), (nb078_alpha_dummy_390 g)), ((nb078_alpha_dummy_385),
        (nb078_alpha_dummy_386 g)), ((nb078_alpha_dummy_381), (nb078_alpha_dummy_383 g)),
        ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)), ((nb078_alpha_dummy_407),
        (nb078_alpha_dummy_408 g)), ((nb078_alpha_dummy_405), (nb078_alpha_dummy_406 g)),
        ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)), ((nb078_alpha_dummy_373),
        (nb078_alpha_dummy_375 g)), ((nb078_alpha_dummy_403), (nb078_alpha_dummy_404 g)),
        ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)), ((nb078_alpha_dummy_368),
        (nb078_alpha_dummy_370 g)), ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
        ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_571),
        (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575),
        (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠
        (nb078_alpha_dummy_395) from (by
          unfold
            nb078_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0388)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_396 g) from (by
          unfold
            nb078_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0389
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_393)
        from (by
          unfold
            nb078_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0386)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_394 g) from (by
          unfold
            nb078_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0387
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_395)
        from (by
          unfold
            nb078_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0392)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_396 g) from (by
          unfold
            nb078_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0393
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_393)
        from (by
          unfold
            nb078_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0390)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_394 g) from (by
          unfold
            nb078_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0391
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_395) from (by
          unfold
            nb078_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0388)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_396 g) from (by
          unfold
            nb078_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0389
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_393)
        from (by
          unfold
            nb078_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0386)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_394 g) from (by
          unfold
            nb078_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0387
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_395)
        from (by
          unfold
            nb078_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0392)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_396 g) from (by
          unfold
            nb078_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0393
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_393)
        from (by
          unfold
            nb078_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0390)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_394 g) from (by
          unfold
            nb078_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0391
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_389), (nb078_alpha_dummy_392 g)), ((nb078_alpha_dummy_388),
        (nb078_alpha_dummy_391 g)), ((nb078_alpha_dummy_387), (nb078_alpha_dummy_390 g)),
        ((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)), ((nb078_alpha_dummy_381),
        (nb078_alpha_dummy_383 g)), ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)),
        ((nb078_alpha_dummy_407), (nb078_alpha_dummy_408 g)), ((nb078_alpha_dummy_405),
        (nb078_alpha_dummy_406 g)), ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)),
        ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)), ((nb078_alpha_dummy_403),
        (nb078_alpha_dummy_404 g)), ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)),
        ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)), ((nb078_alpha_dummy_367),
        (nb078_alpha_dummy_369 g)), ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)),
        ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570),
        (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
        ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_381))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_381))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠
        (nb078_alpha_dummy_399) from (by
          unfold
            nb078_alpha_dummy_399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0396)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_400 g) from (by
          unfold
            nb078_alpha_dummy_400;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0397
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_397)
        from (by
          unfold
            nb078_alpha_dummy_397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0394)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_398 g) from (by
          unfold
            nb078_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0395
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_399)
        from (by
          unfold
            nb078_alpha_dummy_399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0396)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_400 g) from (by
          unfold
            nb078_alpha_dummy_400;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0397
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_397)
        from (by
          unfold
            nb078_alpha_dummy_397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0394)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_398 g) from (by
          unfold
            nb078_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0395
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_401) from (by
          unfold
            nb078_alpha_dummy_401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0400)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_402 g) from (by
          unfold
            nb078_alpha_dummy_402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0401
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_397)
        from (by
          unfold
            nb078_alpha_dummy_397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0398)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_398 g) from (by
          unfold
            nb078_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0399
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠
        (nb078_alpha_dummy_401) from (by
          unfold
            nb078_alpha_dummy_401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0400)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_402 g) from (by
          unfold
            nb078_alpha_dummy_402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0401
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_397)
        from (by
          unfold
            nb078_alpha_dummy_397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0398)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_398 g) from (by
          unfold
            nb078_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0399
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_385) from (by
                                  unfold nb078_alpha_dummy_385;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0382) 0))))
                              (show (nb078_alpha_dummy_383 g) ≠ (nb078_alpha_dummy_386 g) from
                                (by
                                  unfold nb078_alpha_dummy_386;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0383 g) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)),
                              ((nb078_alpha_dummy_381), (nb078_alpha_dummy_383 g)),
                              ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)),
                              ((nb078_alpha_dummy_407), (nb078_alpha_dummy_408 g)),
                              ((nb078_alpha_dummy_405), (nb078_alpha_dummy_406 g)),
                              ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)),
                              ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)),
                              ((nb078_alpha_dummy_403), (nb078_alpha_dummy_404 g)),
                              ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)),
                              ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
                              ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
                              ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)),
                              ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                              ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                              ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                              ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                              ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                              ((nb078_alpha_dummy_003), x)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_385) from (by
                                unfold nb078_alpha_dummy_385;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0382) 0))))
                            (show (nb078_alpha_dummy_383 g) ≠ (nb078_alpha_dummy_386 g) from (by
                                unfold nb078_alpha_dummy_386;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0383 g) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_385) from (by
                                  unfold nb078_alpha_dummy_385;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0382) 0))))
                              (show (nb078_alpha_dummy_383 g) ≠ (nb078_alpha_dummy_386 g) from
                                (by
                                  unfold nb078_alpha_dummy_386;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0383 g) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)),
                              ((nb078_alpha_dummy_381), (nb078_alpha_dummy_383 g)),
                              ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)),
                              ((nb078_alpha_dummy_407), (nb078_alpha_dummy_408 g)),
                              ((nb078_alpha_dummy_405), (nb078_alpha_dummy_406 g)),
                              ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)),
                              ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)),
                              ((nb078_alpha_dummy_403), (nb078_alpha_dummy_404 g)),
                              ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)),
                              ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
                              ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
                              ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)),
                              ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                              ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                              ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                              ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                              ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                              ((nb078_alpha_dummy_003), x)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
