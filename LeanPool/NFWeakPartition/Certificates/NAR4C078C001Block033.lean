/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block032

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part102`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0076`. -/
@[expose]
noncomputable def nb078SplitAlpha0076 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078AlphaDummy759), (nb078AlphaDummy760 g)),
        ((nb078AlphaDummy728), (nb078AlphaDummy730 g)),
        ((nb078AlphaDummy727), (nb078AlphaDummy729 g)),
        ((nb078AlphaDummy757), (nb078AlphaDummy758 g)),
        ((nb078AlphaDummy731), (nb078AlphaDummy732 g)),
        ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
        ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
        ((nb078AlphaDummy565), (nb078AlphaDummy566 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.classMem (Class.cv (nb078AlphaDummy759))
        (synCcompl (synCphi (Class.cv (nb078AlphaDummy728)))))
      (Wff.classMem (Class.cv (nb078AlphaDummy760 g))
        (synCcompl (synCphi (Class.cv (nb078AlphaDummy730 g))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb078AlphaDummy728) ≠ (nb078AlphaDummy735) from (by
                            unfold nb078AlphaDummy735;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0766) 0))))
                        (show (nb078AlphaDummy730 g) ≠ (nb078AlphaDummy737 g) from (by
                            unfold nb078AlphaDummy737;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0767 g) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy728) ≠ (nb078AlphaDummy736) from (by
                              unfold nb078AlphaDummy736;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0766) 1))))
                          (show (nb078AlphaDummy730 g) ≠ (nb078AlphaDummy738 g) from (by
                              unfold nb078AlphaDummy738;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0767 g) 1))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy728) ≠ (nb078AlphaDummy761) from (by
                                unfold nb078AlphaDummy761;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0796) 0))))
                            (show (nb078AlphaDummy730 g) ≠ (nb078AlphaDummy762 g) from (by
                                unfold nb078AlphaDummy762;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0797 g) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy728) ≠ (nb078AlphaDummy759) from (by
                                  unfold nb078AlphaDummy759;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0794) 0))))
                              (show (nb078AlphaDummy730 g) ≠ (nb078AlphaDummy760 g) from
                                (by
                                  unfold nb078AlphaDummy760;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0795 g) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there
                        (freshVar_injective (((Class.cv (nb078AlphaDummy728))).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv (nb078AlphaDummy730 g))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078AlphaDummy735) ≠
        (nb078AlphaDummy742) from (by
          unfold nb078AlphaDummy742;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0770) 1)))) (show (nb078AlphaDummy737 g) ≠
        (nb078AlphaDummy745 g) from (by
          unfold nb078AlphaDummy745;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0771 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy735) ≠ (nb078AlphaDummy741) from (by
          unfold nb078AlphaDummy741;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0770) 0)))) (show (nb078AlphaDummy737 g) ≠
        (nb078AlphaDummy744 g) from (by
          unfold nb078AlphaDummy744;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0771 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy735) ≠ (nb078AlphaDummy739) from (by
          unfold nb078AlphaDummy739;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0768) 0)))) (show (nb078AlphaDummy737 g) ≠
        (nb078AlphaDummy740 g) from (by
          unfold nb078AlphaDummy740;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0769 g) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy743), (nb078AlphaDummy746 g)), ((nb078AlphaDummy742),
        (nb078AlphaDummy745 g)), ((nb078AlphaDummy741), (nb078AlphaDummy744 g)),
        ((nb078AlphaDummy739), (nb078AlphaDummy740 g)), ((nb078AlphaDummy735),
        (nb078AlphaDummy737 g)), ((nb078AlphaDummy736), (nb078AlphaDummy738 g)),
        ((nb078AlphaDummy761), (nb078AlphaDummy762 g)), ((nb078AlphaDummy759),
        (nb078AlphaDummy760 g)), ((nb078AlphaDummy728), (nb078AlphaDummy730 g)),
        ((nb078AlphaDummy727), (nb078AlphaDummy729 g)), ((nb078AlphaDummy757),
        (nb078AlphaDummy758 g)), ((nb078AlphaDummy731), (nb078AlphaDummy732 g)),
        ((nb078AlphaDummy571), (nb078AlphaDummy574 g)), ((nb078AlphaDummy570),
        (nb078AlphaDummy573 g)), ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
        ((nb078AlphaDummy575), (nb078AlphaDummy576 g)), ((nb078AlphaDummy567),
        (nb078AlphaDummy568 g)), ((nb078AlphaDummy565), (nb078AlphaDummy566 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy742) ≠ (nb078AlphaDummy749) from (by
          unfold
            nb078AlphaDummy749;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0774)
                  0)))) (show (nb078AlphaDummy745 g) ≠ (nb078AlphaDummy750 g) from (by
          unfold
            nb078AlphaDummy750;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0775
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy742) ≠ (nb078AlphaDummy747)
        from (by
          unfold
            nb078AlphaDummy747;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0772)
                  0)))) (show (nb078AlphaDummy745 g) ≠ (nb078AlphaDummy748 g) from (by
          unfold
            nb078AlphaDummy748;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0773
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy735))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy737 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy743) ≠ (nb078AlphaDummy749)
        from (by
          unfold
            nb078AlphaDummy749;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0778)
                  0)))) (show (nb078AlphaDummy746 g) ≠ (nb078AlphaDummy750 g) from (by
          unfold
            nb078AlphaDummy750;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0779
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy743) ≠ (nb078AlphaDummy747)
        from (by
          unfold
            nb078AlphaDummy747;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0776)
                  0)))) (show (nb078AlphaDummy746 g) ≠ (nb078AlphaDummy748 g) from (by
          unfold
            nb078AlphaDummy748;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0777
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy742) ≠ (nb078AlphaDummy749) from (by
          unfold
            nb078AlphaDummy749;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0774)
                  0)))) (show (nb078AlphaDummy745 g) ≠ (nb078AlphaDummy750 g) from (by
          unfold
            nb078AlphaDummy750;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0775
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy742) ≠ (nb078AlphaDummy747)
        from (by
          unfold
            nb078AlphaDummy747;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0772)
                  0)))) (show (nb078AlphaDummy745 g) ≠ (nb078AlphaDummy748 g) from (by
          unfold
            nb078AlphaDummy748;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0773
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy735))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy737 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy743) ≠ (nb078AlphaDummy749)
        from (by
          unfold
            nb078AlphaDummy749;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0778)
                  0)))) (show (nb078AlphaDummy746 g) ≠ (nb078AlphaDummy750 g) from (by
          unfold
            nb078AlphaDummy750;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0779
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy743) ≠ (nb078AlphaDummy747)
        from (by
          unfold
            nb078AlphaDummy747;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0776)
                  0)))) (show (nb078AlphaDummy746 g) ≠ (nb078AlphaDummy748 g) from (by
          unfold
            nb078AlphaDummy748;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0777
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy743), (nb078AlphaDummy746 g)), ((nb078AlphaDummy742),
        (nb078AlphaDummy745 g)), ((nb078AlphaDummy741), (nb078AlphaDummy744 g)),
        ((nb078AlphaDummy739), (nb078AlphaDummy740 g)), ((nb078AlphaDummy735),
        (nb078AlphaDummy737 g)), ((nb078AlphaDummy736), (nb078AlphaDummy738 g)),
        ((nb078AlphaDummy761), (nb078AlphaDummy762 g)), ((nb078AlphaDummy759),
        (nb078AlphaDummy760 g)), ((nb078AlphaDummy728), (nb078AlphaDummy730 g)),
        ((nb078AlphaDummy727), (nb078AlphaDummy729 g)), ((nb078AlphaDummy757),
        (nb078AlphaDummy758 g)), ((nb078AlphaDummy731), (nb078AlphaDummy732 g)),
        ((nb078AlphaDummy571), (nb078AlphaDummy574 g)), ((nb078AlphaDummy570),
        (nb078AlphaDummy573 g)), ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
        ((nb078AlphaDummy575), (nb078AlphaDummy576 g)), ((nb078AlphaDummy567),
        (nb078AlphaDummy568 g)), ((nb078AlphaDummy565), (nb078AlphaDummy566 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy735))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy737 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy735))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy737 g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy742) ≠ (nb078AlphaDummy753) from (by
          unfold
            nb078AlphaDummy753;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0782)
                  0)))) (show (nb078AlphaDummy745 g) ≠ (nb078AlphaDummy754 g) from (by
          unfold
            nb078AlphaDummy754;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0783
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy742) ≠ (nb078AlphaDummy751)
        from (by
          unfold
            nb078AlphaDummy751;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0780)
                  0)))) (show (nb078AlphaDummy745 g) ≠ (nb078AlphaDummy752 g) from (by
          unfold
            nb078AlphaDummy752;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0781
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy735))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy737 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy742) ≠ (nb078AlphaDummy753)
        from (by
          unfold
            nb078AlphaDummy753;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0782)
                  0)))) (show (nb078AlphaDummy745 g) ≠ (nb078AlphaDummy754 g) from (by
          unfold
            nb078AlphaDummy754;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0783
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy742) ≠ (nb078AlphaDummy751)
        from (by
          unfold
            nb078AlphaDummy751;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0780)
                  0)))) (show (nb078AlphaDummy745 g) ≠ (nb078AlphaDummy752 g) from (by
          unfold
            nb078AlphaDummy752;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0781
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy735))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy737 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy743) ≠ (nb078AlphaDummy755) from (by
          unfold
            nb078AlphaDummy755;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0786)
                  0)))) (show (nb078AlphaDummy746 g) ≠ (nb078AlphaDummy756 g) from (by
          unfold
            nb078AlphaDummy756;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0787
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy743) ≠ (nb078AlphaDummy751)
        from (by
          unfold
            nb078AlphaDummy751;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0784)
                  0)))) (show (nb078AlphaDummy746 g) ≠ (nb078AlphaDummy752 g) from (by
          unfold
            nb078AlphaDummy752;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0785
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy743) ≠
        (nb078AlphaDummy755) from (by
          unfold
            nb078AlphaDummy755;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0786)
                  0)))) (show (nb078AlphaDummy746 g) ≠ (nb078AlphaDummy756 g) from (by
          unfold
            nb078AlphaDummy756;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0787
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy743) ≠ (nb078AlphaDummy751)
        from (by
          unfold
            nb078AlphaDummy751;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0784)
                  0)))) (show (nb078AlphaDummy746 g) ≠ (nb078AlphaDummy752 g) from (by
          unfold
            nb078AlphaDummy752;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0785
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy735) ≠ (nb078AlphaDummy739) from
                                    (by
                                      unfold nb078AlphaDummy739;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0768)
                                              0)))) (show
                                    (nb078AlphaDummy737 g) ≠ (nb078AlphaDummy740 g) from
                                    (by
                                      unfold nb078AlphaDummy740;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0769 g)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed
                                [((nb078AlphaDummy739), (nb078AlphaDummy740 g)),
                                  ((nb078AlphaDummy735), (nb078AlphaDummy737 g)),
                                  ((nb078AlphaDummy736), (nb078AlphaDummy738 g)),
                                  ((nb078AlphaDummy761), (nb078AlphaDummy762 g)),
                                  ((nb078AlphaDummy759), (nb078AlphaDummy760 g)),
                                  ((nb078AlphaDummy728), (nb078AlphaDummy730 g)),
                                  ((nb078AlphaDummy727), (nb078AlphaDummy729 g)),
                                  ((nb078AlphaDummy757), (nb078AlphaDummy758 g)),
                                  ((nb078AlphaDummy731), (nb078AlphaDummy732 g)),
                                  ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                                  ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                                  ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                                  ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                                  ((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
                                  ((nb078AlphaDummy565), (nb078AlphaDummy566 g)),
                                  ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                  ((nb078AlphaDummy003), x)]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb078AlphaDummy735) ≠ (nb078AlphaDummy739) from (by
                                    unfold nb078AlphaDummy739;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0768) 0)))) (show
                                  (nb078AlphaDummy737 g) ≠ (nb078AlphaDummy740 g) from (by
                                    unfold nb078AlphaDummy740;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0769 g)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy735) ≠ (nb078AlphaDummy739) from
                                    (by
                                      unfold nb078AlphaDummy739;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0768)
                                              0)))) (show
                                    (nb078AlphaDummy737 g) ≠ (nb078AlphaDummy740 g) from
                                    (by
                                      unfold nb078AlphaDummy740;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0769 g)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed
                                [((nb078AlphaDummy739), (nb078AlphaDummy740 g)),
                                  ((nb078AlphaDummy735), (nb078AlphaDummy737 g)),
                                  ((nb078AlphaDummy736), (nb078AlphaDummy738 g)),
                                  ((nb078AlphaDummy761), (nb078AlphaDummy762 g)),
                                  ((nb078AlphaDummy759), (nb078AlphaDummy760 g)),
                                  ((nb078AlphaDummy728), (nb078AlphaDummy730 g)),
                                  ((nb078AlphaDummy727), (nb078AlphaDummy729 g)),
                                  ((nb078AlphaDummy757), (nb078AlphaDummy758 g)),
                                  ((nb078AlphaDummy731), (nb078AlphaDummy732 g)),
                                  ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                                  ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                                  ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                                  ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                                  ((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
                                  ((nb078AlphaDummy565), (nb078AlphaDummy566 g)),
                                  ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                  ((nb078AlphaDummy003), x)]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb078AlphaDummy728) ≠ (nb078AlphaDummy735) from (by
                            unfold nb078AlphaDummy735;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0766) 0))))
                        (show (nb078AlphaDummy730 g) ≠ (nb078AlphaDummy737 g) from (by
                            unfold nb078AlphaDummy737;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0767 g) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy728) ≠ (nb078AlphaDummy736) from (by
                              unfold nb078AlphaDummy736;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0766) 1))))
                          (show (nb078AlphaDummy730 g) ≠ (nb078AlphaDummy738 g) from (by
                              unfold nb078AlphaDummy738;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0767 g) 1))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy728) ≠ (nb078AlphaDummy761) from (by
                                unfold nb078AlphaDummy761;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0796) 0))))
                            (show (nb078AlphaDummy730 g) ≠ (nb078AlphaDummy762 g) from (by
                                unfold nb078AlphaDummy762;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0797 g) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy728) ≠ (nb078AlphaDummy759) from (by
                                  unfold nb078AlphaDummy759;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0794) 0))))
                              (show (nb078AlphaDummy730 g) ≠ (nb078AlphaDummy760 g) from
                                (by
                                  unfold nb078AlphaDummy760;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0795 g) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there
                        (freshVar_injective (((Class.cv (nb078AlphaDummy728))).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv (nb078AlphaDummy730 g))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078AlphaDummy735) ≠
        (nb078AlphaDummy742) from (by
          unfold nb078AlphaDummy742;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0770) 1)))) (show (nb078AlphaDummy737 g) ≠
        (nb078AlphaDummy745 g) from (by
          unfold nb078AlphaDummy745;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0771 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy735) ≠ (nb078AlphaDummy741) from (by
          unfold nb078AlphaDummy741;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0770) 0)))) (show (nb078AlphaDummy737 g) ≠
        (nb078AlphaDummy744 g) from (by
          unfold nb078AlphaDummy744;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0771 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy735) ≠ (nb078AlphaDummy739) from (by
          unfold nb078AlphaDummy739;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0768) 0)))) (show (nb078AlphaDummy737 g) ≠
        (nb078AlphaDummy740 g) from (by
          unfold nb078AlphaDummy740;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0769 g) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy743), (nb078AlphaDummy746 g)), ((nb078AlphaDummy742),
        (nb078AlphaDummy745 g)), ((nb078AlphaDummy741), (nb078AlphaDummy744 g)),
        ((nb078AlphaDummy739), (nb078AlphaDummy740 g)), ((nb078AlphaDummy735),
        (nb078AlphaDummy737 g)), ((nb078AlphaDummy736), (nb078AlphaDummy738 g)),
        ((nb078AlphaDummy761), (nb078AlphaDummy762 g)), ((nb078AlphaDummy759),
        (nb078AlphaDummy760 g)), ((nb078AlphaDummy728), (nb078AlphaDummy730 g)),
        ((nb078AlphaDummy727), (nb078AlphaDummy729 g)), ((nb078AlphaDummy757),
        (nb078AlphaDummy758 g)), ((nb078AlphaDummy731), (nb078AlphaDummy732 g)),
        ((nb078AlphaDummy571), (nb078AlphaDummy574 g)), ((nb078AlphaDummy570),
        (nb078AlphaDummy573 g)), ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
        ((nb078AlphaDummy575), (nb078AlphaDummy576 g)), ((nb078AlphaDummy567),
        (nb078AlphaDummy568 g)), ((nb078AlphaDummy565), (nb078AlphaDummy566 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy742) ≠ (nb078AlphaDummy749) from (by
          unfold
            nb078AlphaDummy749;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0774)
                  0)))) (show (nb078AlphaDummy745 g) ≠ (nb078AlphaDummy750 g) from (by
          unfold
            nb078AlphaDummy750;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0775
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy742) ≠ (nb078AlphaDummy747)
        from (by
          unfold
            nb078AlphaDummy747;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0772)
                  0)))) (show (nb078AlphaDummy745 g) ≠ (nb078AlphaDummy748 g) from (by
          unfold
            nb078AlphaDummy748;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0773
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy735))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy737 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy743) ≠ (nb078AlphaDummy749)
        from (by
          unfold
            nb078AlphaDummy749;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0778)
                  0)))) (show (nb078AlphaDummy746 g) ≠ (nb078AlphaDummy750 g) from (by
          unfold
            nb078AlphaDummy750;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0779
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy743) ≠ (nb078AlphaDummy747)
        from (by
          unfold
            nb078AlphaDummy747;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0776)
                  0)))) (show (nb078AlphaDummy746 g) ≠ (nb078AlphaDummy748 g) from (by
          unfold
            nb078AlphaDummy748;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0777
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy742) ≠ (nb078AlphaDummy749) from (by
          unfold
            nb078AlphaDummy749;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0774)
                  0)))) (show (nb078AlphaDummy745 g) ≠ (nb078AlphaDummy750 g) from (by
          unfold
            nb078AlphaDummy750;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0775
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy742) ≠ (nb078AlphaDummy747)
        from (by
          unfold
            nb078AlphaDummy747;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0772)
                  0)))) (show (nb078AlphaDummy745 g) ≠ (nb078AlphaDummy748 g) from (by
          unfold
            nb078AlphaDummy748;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0773
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy735))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy737 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy743) ≠ (nb078AlphaDummy749)
        from (by
          unfold
            nb078AlphaDummy749;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0778)
                  0)))) (show (nb078AlphaDummy746 g) ≠ (nb078AlphaDummy750 g) from (by
          unfold
            nb078AlphaDummy750;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0779
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy743) ≠ (nb078AlphaDummy747)
        from (by
          unfold
            nb078AlphaDummy747;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0776)
                  0)))) (show (nb078AlphaDummy746 g) ≠ (nb078AlphaDummy748 g) from (by
          unfold
            nb078AlphaDummy748;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0777
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy743), (nb078AlphaDummy746 g)), ((nb078AlphaDummy742),
        (nb078AlphaDummy745 g)), ((nb078AlphaDummy741), (nb078AlphaDummy744 g)),
        ((nb078AlphaDummy739), (nb078AlphaDummy740 g)), ((nb078AlphaDummy735),
        (nb078AlphaDummy737 g)), ((nb078AlphaDummy736), (nb078AlphaDummy738 g)),
        ((nb078AlphaDummy761), (nb078AlphaDummy762 g)), ((nb078AlphaDummy759),
        (nb078AlphaDummy760 g)), ((nb078AlphaDummy728), (nb078AlphaDummy730 g)),
        ((nb078AlphaDummy727), (nb078AlphaDummy729 g)), ((nb078AlphaDummy757),
        (nb078AlphaDummy758 g)), ((nb078AlphaDummy731), (nb078AlphaDummy732 g)),
        ((nb078AlphaDummy571), (nb078AlphaDummy574 g)), ((nb078AlphaDummy570),
        (nb078AlphaDummy573 g)), ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
        ((nb078AlphaDummy575), (nb078AlphaDummy576 g)), ((nb078AlphaDummy567),
        (nb078AlphaDummy568 g)), ((nb078AlphaDummy565), (nb078AlphaDummy566 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy735))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy737 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy735))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy737 g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy742) ≠ (nb078AlphaDummy753) from (by
          unfold
            nb078AlphaDummy753;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0782)
                  0)))) (show (nb078AlphaDummy745 g) ≠ (nb078AlphaDummy754 g) from (by
          unfold
            nb078AlphaDummy754;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0783
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy742) ≠ (nb078AlphaDummy751)
        from (by
          unfold
            nb078AlphaDummy751;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0780)
                  0)))) (show (nb078AlphaDummy745 g) ≠ (nb078AlphaDummy752 g) from (by
          unfold
            nb078AlphaDummy752;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0781
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy735))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy737 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy742) ≠ (nb078AlphaDummy753)
        from (by
          unfold
            nb078AlphaDummy753;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0782)
                  0)))) (show (nb078AlphaDummy745 g) ≠ (nb078AlphaDummy754 g) from (by
          unfold
            nb078AlphaDummy754;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0783
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy742) ≠ (nb078AlphaDummy751)
        from (by
          unfold
            nb078AlphaDummy751;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0780)
                  0)))) (show (nb078AlphaDummy745 g) ≠ (nb078AlphaDummy752 g) from (by
          unfold
            nb078AlphaDummy752;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0781
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy735))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy737 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy743) ≠ (nb078AlphaDummy755) from (by
          unfold
            nb078AlphaDummy755;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0786)
                  0)))) (show (nb078AlphaDummy746 g) ≠ (nb078AlphaDummy756 g) from (by
          unfold
            nb078AlphaDummy756;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0787
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy743) ≠ (nb078AlphaDummy751)
        from (by
          unfold
            nb078AlphaDummy751;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0784)
                  0)))) (show (nb078AlphaDummy746 g) ≠ (nb078AlphaDummy752 g) from (by
          unfold
            nb078AlphaDummy752;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0785
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy743) ≠
        (nb078AlphaDummy755) from (by
          unfold
            nb078AlphaDummy755;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0786)
                  0)))) (show (nb078AlphaDummy746 g) ≠ (nb078AlphaDummy756 g) from (by
          unfold
            nb078AlphaDummy756;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0787
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy743) ≠ (nb078AlphaDummy751)
        from (by
          unfold
            nb078AlphaDummy751;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0784)
                  0)))) (show (nb078AlphaDummy746 g) ≠ (nb078AlphaDummy752 g) from (by
          unfold
            nb078AlphaDummy752;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0785
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy735) ≠ (nb078AlphaDummy739) from
                                    (by
                                      unfold nb078AlphaDummy739;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0768)
                                              0)))) (show
                                    (nb078AlphaDummy737 g) ≠ (nb078AlphaDummy740 g) from
                                    (by
                                      unfold nb078AlphaDummy740;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0769 g)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed
                                [((nb078AlphaDummy739), (nb078AlphaDummy740 g)),
                                  ((nb078AlphaDummy735), (nb078AlphaDummy737 g)),
                                  ((nb078AlphaDummy736), (nb078AlphaDummy738 g)),
                                  ((nb078AlphaDummy761), (nb078AlphaDummy762 g)),
                                  ((nb078AlphaDummy759), (nb078AlphaDummy760 g)),
                                  ((nb078AlphaDummy728), (nb078AlphaDummy730 g)),
                                  ((nb078AlphaDummy727), (nb078AlphaDummy729 g)),
                                  ((nb078AlphaDummy757), (nb078AlphaDummy758 g)),
                                  ((nb078AlphaDummy731), (nb078AlphaDummy732 g)),
                                  ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                                  ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                                  ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                                  ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                                  ((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
                                  ((nb078AlphaDummy565), (nb078AlphaDummy566 g)),
                                  ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                  ((nb078AlphaDummy003), x)]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb078AlphaDummy735) ≠ (nb078AlphaDummy739) from (by
                                    unfold nb078AlphaDummy739;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0768) 0)))) (show
                                  (nb078AlphaDummy737 g) ≠ (nb078AlphaDummy740 g) from (by
                                    unfold nb078AlphaDummy740;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0769 g)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy735) ≠ (nb078AlphaDummy739) from
                                    (by
                                      unfold nb078AlphaDummy739;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0768)
                                              0)))) (show
                                    (nb078AlphaDummy737 g) ≠ (nb078AlphaDummy740 g) from
                                    (by
                                      unfold nb078AlphaDummy740;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0769 g)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed
                                [((nb078AlphaDummy739), (nb078AlphaDummy740 g)),
                                  ((nb078AlphaDummy735), (nb078AlphaDummy737 g)),
                                  ((nb078AlphaDummy736), (nb078AlphaDummy738 g)),
                                  ((nb078AlphaDummy761), (nb078AlphaDummy762 g)),
                                  ((nb078AlphaDummy759), (nb078AlphaDummy760 g)),
                                  ((nb078AlphaDummy728), (nb078AlphaDummy730 g)),
                                  ((nb078AlphaDummy727), (nb078AlphaDummy729 g)),
                                  ((nb078AlphaDummy757), (nb078AlphaDummy758 g)),
                                  ((nb078AlphaDummy731), (nb078AlphaDummy732 g)),
                                  ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                                  ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                                  ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                                  ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                                  ((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
                                  ((nb078AlphaDummy565), (nb078AlphaDummy566 g)),
                                  ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                  ((nb078AlphaDummy003), x)]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part103`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0077`. -/
@[expose]
noncomputable def nb078SplitAlpha0077 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078AlphaDummy379), (nb078AlphaDummy380 g)),
        ((nb078AlphaDummy377), (nb078AlphaDummy378 g)),
        ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
        ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
        ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
        ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
        ((nb078AlphaDummy565), (nb078AlphaDummy566 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy379))
          (Class.cab (nb078AlphaDummy373)
            (synWrex (nb078AlphaDummy374) (Class.cv (nb078AlphaDummy367))
              (Wff.classEq (Class.cv (nb078AlphaDummy373))
                (synCphi (Class.cv (nb078AlphaDummy374))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy379)) (Class.cab (nb078AlphaDummy373)
              (synWrex (nb078AlphaDummy374) (Class.cv (nb078AlphaDummy367))
                (Wff.classEq (Class.cv (nb078AlphaDummy373))
                  (synCphi (Class.cv (nb078AlphaDummy374)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy380 g))
          (Class.cab (nb078AlphaDummy375 g)
            (synWrex (nb078AlphaDummy376 g) (Class.cv (nb078AlphaDummy369 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy375 g))
                (synCphi (Class.cv (nb078AlphaDummy376 g))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy380 g))
            (Class.cab (nb078AlphaDummy375 g)
              (synWrex (nb078AlphaDummy376 g) (Class.cv (nb078AlphaDummy369 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy375 g))
                  (synCphi (Class.cv (nb078AlphaDummy376 g))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy374) from
                    (by
                      unfold nb078AlphaDummy374;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0374) 1))))
                  (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy376 g) from (by
                      unfold nb078AlphaDummy376;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0376 g) 1))))
                  (TAlphaVar.there (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy373) from
                      (by
                        unfold nb078AlphaDummy373;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0374) 0))))
                    (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy375 g) from (by
                        unfold nb078AlphaDummy375;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0376 g) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy379) from (by
                          unfold nb078AlphaDummy379;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0378) 0))))
                      (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy380 g) from (by
                          unfold nb078AlphaDummy380;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0379 g) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy377) from (by
                            unfold nb078AlphaDummy377;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0375) 0))))
                        (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy378 g) from (by
                            unfold nb078AlphaDummy378;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0377 g) 0))))
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy001))).fv)
                            (by decide)) (freshVar_injective (((Class.cv g)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy367))).fv ∪
                      ((Class.cv (nb078AlphaDummy368))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078AlphaDummy369 g))).fv ∪
                      ((Class.cv (nb078AlphaDummy370 g))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy374) ≠ (nb078AlphaDummy381) from (by
                              unfold nb078AlphaDummy381;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0380) 0))))
                          (show (nb078AlphaDummy376 g) ≠ (nb078AlphaDummy383 g) from (by
                              unfold nb078AlphaDummy383;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0381 g) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy374) ≠ (nb078AlphaDummy382) from (by
                                unfold nb078AlphaDummy382;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0380) 1))))
                            (show (nb078AlphaDummy376 g) ≠ (nb078AlphaDummy384 g) from (by
                                unfold nb078AlphaDummy384;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0381 g) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy374))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy376 g))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy381) ≠ (nb078AlphaDummy388) from (by
          unfold nb078AlphaDummy388;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0384) 1)))) (show (nb078AlphaDummy383 g) ≠
        (nb078AlphaDummy391 g) from (by
          unfold nb078AlphaDummy391;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0385 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy381) ≠ (nb078AlphaDummy387) from (by
          unfold nb078AlphaDummy387;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0384) 0)))) (show (nb078AlphaDummy383 g) ≠
        (nb078AlphaDummy390 g) from (by
          unfold nb078AlphaDummy390;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0385 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy381) ≠ (nb078AlphaDummy385) from (by
          unfold nb078AlphaDummy385;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0382) 0)))) (show (nb078AlphaDummy383 g) ≠
        (nb078AlphaDummy386 g) from (by
          unfold nb078AlphaDummy386;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0383 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy389), (nb078AlphaDummy392 g)), ((nb078AlphaDummy388),
        (nb078AlphaDummy391 g)), ((nb078AlphaDummy387), (nb078AlphaDummy390 g)),
        ((nb078AlphaDummy385), (nb078AlphaDummy386 g)), ((nb078AlphaDummy381),
        (nb078AlphaDummy383 g)), ((nb078AlphaDummy382), (nb078AlphaDummy384 g)),
        ((nb078AlphaDummy374), (nb078AlphaDummy376 g)), ((nb078AlphaDummy373),
        (nb078AlphaDummy375 g)), ((nb078AlphaDummy379), (nb078AlphaDummy380 g)),
        ((nb078AlphaDummy377), (nb078AlphaDummy378 g)), ((nb078AlphaDummy368),
        (nb078AlphaDummy370 g)), ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)), ((nb078AlphaDummy571),
        (nb078AlphaDummy574 g)), ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)), ((nb078AlphaDummy575),
        (nb078AlphaDummy576 g)), ((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
        ((nb078AlphaDummy565), (nb078AlphaDummy566 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy395) from (by
          unfold
            nb078AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0388)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy396 g) from (by
          unfold
            nb078AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0389
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy393)
        from (by
          unfold
            nb078AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0386)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy394 g) from (by
          unfold
            nb078AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0387
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy395)
        from (by
          unfold
            nb078AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0392)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy396 g) from (by
          unfold
            nb078AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0393
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy393)
        from (by
          unfold
            nb078AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0390)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy394 g) from (by
          unfold
            nb078AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0391
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy395) from (by
          unfold
            nb078AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0388)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy396 g) from (by
          unfold
            nb078AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0389
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy393)
        from (by
          unfold
            nb078AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0386)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy394 g) from (by
          unfold
            nb078AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0387
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy395)
        from (by
          unfold
            nb078AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0392)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy396 g) from (by
          unfold
            nb078AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0393
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy393)
        from (by
          unfold
            nb078AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0390)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy394 g) from (by
          unfold
            nb078AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0391
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy389), (nb078AlphaDummy392 g)), ((nb078AlphaDummy388),
        (nb078AlphaDummy391 g)), ((nb078AlphaDummy387), (nb078AlphaDummy390 g)),
        ((nb078AlphaDummy385), (nb078AlphaDummy386 g)), ((nb078AlphaDummy381),
        (nb078AlphaDummy383 g)), ((nb078AlphaDummy382), (nb078AlphaDummy384 g)),
        ((nb078AlphaDummy374), (nb078AlphaDummy376 g)), ((nb078AlphaDummy373),
        (nb078AlphaDummy375 g)), ((nb078AlphaDummy379), (nb078AlphaDummy380 g)),
        ((nb078AlphaDummy377), (nb078AlphaDummy378 g)), ((nb078AlphaDummy368),
        (nb078AlphaDummy370 g)), ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)), ((nb078AlphaDummy571),
        (nb078AlphaDummy574 g)), ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)), ((nb078AlphaDummy575),
        (nb078AlphaDummy576 g)), ((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
        ((nb078AlphaDummy565), (nb078AlphaDummy566 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy381))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy383 g))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy388) ≠
        (nb078AlphaDummy399) from (by
          unfold
            nb078AlphaDummy399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0396)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy400 g) from (by
          unfold
            nb078AlphaDummy400;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0397
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy397)
        from (by
          unfold
            nb078AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0394)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy398 g) from (by
          unfold
            nb078AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0395
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy399)
        from (by
          unfold
            nb078AlphaDummy399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0396)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy400 g) from (by
          unfold
            nb078AlphaDummy400;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0397
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy397)
        from (by
          unfold
            nb078AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0394)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy398 g) from (by
          unfold
            nb078AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0395
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy401) from (by
          unfold
            nb078AlphaDummy401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0400)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy402 g) from (by
          unfold
            nb078AlphaDummy402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0401
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy397)
        from (by
          unfold
            nb078AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0398)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy398 g) from (by
          unfold
            nb078AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0399
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy389) ≠
        (nb078AlphaDummy401) from (by
          unfold
            nb078AlphaDummy401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0400)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy402 g) from (by
          unfold
            nb078AlphaDummy402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0401
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy397)
        from (by
          unfold
            nb078AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0398)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy398 g) from (by
          unfold
            nb078AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0399
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy381) ≠ (nb078AlphaDummy385) from (by
                                        unfold nb078AlphaDummy385;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0382)
                                                0)))) (show (nb078AlphaDummy383 g) ≠
                                        (nb078AlphaDummy386 g) from (by
                                        unfold nb078AlphaDummy386;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0383 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy385), (nb078AlphaDummy386 g)),
                                    ((nb078AlphaDummy381), (nb078AlphaDummy383 g)),
                                    ((nb078AlphaDummy382), (nb078AlphaDummy384 g)),
                                    ((nb078AlphaDummy374), (nb078AlphaDummy376 g)),
                                    ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
                                    ((nb078AlphaDummy379), (nb078AlphaDummy380 g)),
                                    ((nb078AlphaDummy377), (nb078AlphaDummy378 g)),
                                    ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
                                    ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
                                    ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
                                    ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                                    ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                                    ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                                    ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                                    ((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
                                    ((nb078AlphaDummy565), (nb078AlphaDummy566 g)),
                                    ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy381) ≠ (nb078AlphaDummy385) from
                                    (by
                                      unfold nb078AlphaDummy385;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0382)
                                              0)))) (show
                                    (nb078AlphaDummy383 g) ≠ (nb078AlphaDummy386 g) from
                                    (by
                                      unfold nb078AlphaDummy386;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0383 g)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy381) ≠ (nb078AlphaDummy385) from (by
                                        unfold nb078AlphaDummy385;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0382)
                                                0)))) (show (nb078AlphaDummy383 g) ≠
                                        (nb078AlphaDummy386 g) from (by
                                        unfold nb078AlphaDummy386;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0383 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy385), (nb078AlphaDummy386 g)),
                                    ((nb078AlphaDummy381), (nb078AlphaDummy383 g)),
                                    ((nb078AlphaDummy382), (nb078AlphaDummy384 g)),
                                    ((nb078AlphaDummy374), (nb078AlphaDummy376 g)),
                                    ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
                                    ((nb078AlphaDummy379), (nb078AlphaDummy380 g)),
                                    ((nb078AlphaDummy377), (nb078AlphaDummy378 g)),
                                    ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
                                    ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
                                    ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
                                    ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                                    ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                                    ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                                    ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                                    ((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
                                    ((nb078AlphaDummy565), (nb078AlphaDummy566 g)),
                                    ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy374) from
                      (by
                        unfold nb078AlphaDummy374;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0374) 1))))
                    (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy376 g) from (by
                        unfold nb078AlphaDummy376;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0376 g) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy373) from (by
                          unfold nb078AlphaDummy373;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0374) 0))))
                      (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy375 g) from (by
                          unfold nb078AlphaDummy375;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0376 g) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy379) from (by
                            unfold nb078AlphaDummy379;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0378) 0))))
                        (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy380 g) from (by
                            unfold nb078AlphaDummy380;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0379 g) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy377) from (by
                              unfold nb078AlphaDummy377;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0375) 0))))
                          (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy378 g) from (by
                              unfold nb078AlphaDummy378;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0377 g) 0))))
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy001))).fv)
                              (by decide)) (freshVar_injective (((Class.cv g)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078AlphaDummy367))).fv ∪
                        ((Class.cv (nb078AlphaDummy368))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy369 g))).fv ∪
                        ((Class.cv (nb078AlphaDummy370 g))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy374) ≠ (nb078AlphaDummy381) from (by
                                unfold nb078AlphaDummy381;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0380) 0))))
                            (show (nb078AlphaDummy376 g) ≠ (nb078AlphaDummy383 g) from (by
                                unfold nb078AlphaDummy383;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0381 g) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy374) ≠ (nb078AlphaDummy382) from (by
                                  unfold nb078AlphaDummy382;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0380) 1))))
                              (show (nb078AlphaDummy376 g) ≠ (nb078AlphaDummy384 g) from
                                (by
                                  unfold nb078AlphaDummy384;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0381 g) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy374))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy376 g))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy381) ≠ (nb078AlphaDummy388) from (by
          unfold nb078AlphaDummy388;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0384) 1)))) (show (nb078AlphaDummy383 g) ≠
        (nb078AlphaDummy391 g) from (by
          unfold nb078AlphaDummy391;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0385 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy381) ≠ (nb078AlphaDummy387) from (by
          unfold nb078AlphaDummy387;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0384) 0)))) (show (nb078AlphaDummy383 g) ≠
        (nb078AlphaDummy390 g) from (by
          unfold nb078AlphaDummy390;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0385 g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy381) ≠ (nb078AlphaDummy385)
        from (by
          unfold nb078AlphaDummy385;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0382)
                  0)))) (show (nb078AlphaDummy383 g) ≠ (nb078AlphaDummy386 g) from (by
          unfold nb078AlphaDummy386;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0383 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy389), (nb078AlphaDummy392 g)), ((nb078AlphaDummy388),
        (nb078AlphaDummy391 g)), ((nb078AlphaDummy387), (nb078AlphaDummy390 g)),
        ((nb078AlphaDummy385), (nb078AlphaDummy386 g)), ((nb078AlphaDummy381),
        (nb078AlphaDummy383 g)), ((nb078AlphaDummy382), (nb078AlphaDummy384 g)),
        ((nb078AlphaDummy374), (nb078AlphaDummy376 g)), ((nb078AlphaDummy373),
        (nb078AlphaDummy375 g)), ((nb078AlphaDummy379), (nb078AlphaDummy380 g)),
        ((nb078AlphaDummy377), (nb078AlphaDummy378 g)), ((nb078AlphaDummy368),
        (nb078AlphaDummy370 g)), ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)), ((nb078AlphaDummy571),
        (nb078AlphaDummy574 g)), ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)), ((nb078AlphaDummy575),
        (nb078AlphaDummy576 g)), ((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
        ((nb078AlphaDummy565), (nb078AlphaDummy566 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy395) from (by
          unfold
            nb078AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0388)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy396 g) from (by
          unfold
            nb078AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0389
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy393)
        from (by
          unfold
            nb078AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0386)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy394 g) from (by
          unfold
            nb078AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0387
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy395)
        from (by
          unfold
            nb078AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0392)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy396 g) from (by
          unfold
            nb078AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0393
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy393)
        from (by
          unfold
            nb078AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0390)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy394 g) from (by
          unfold
            nb078AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0391
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy395) from (by
          unfold
            nb078AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0388)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy396 g) from (by
          unfold
            nb078AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0389
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy393)
        from (by
          unfold
            nb078AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0386)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy394 g) from (by
          unfold
            nb078AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0387
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy395)
        from (by
          unfold
            nb078AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0392)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy396 g) from (by
          unfold
            nb078AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0393
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy393)
        from (by
          unfold
            nb078AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0390)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy394 g) from (by
          unfold
            nb078AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0391
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy389), (nb078AlphaDummy392 g)), ((nb078AlphaDummy388),
        (nb078AlphaDummy391 g)), ((nb078AlphaDummy387), (nb078AlphaDummy390 g)),
        ((nb078AlphaDummy385), (nb078AlphaDummy386 g)), ((nb078AlphaDummy381),
        (nb078AlphaDummy383 g)), ((nb078AlphaDummy382), (nb078AlphaDummy384 g)),
        ((nb078AlphaDummy374), (nb078AlphaDummy376 g)), ((nb078AlphaDummy373),
        (nb078AlphaDummy375 g)), ((nb078AlphaDummy379), (nb078AlphaDummy380 g)),
        ((nb078AlphaDummy377), (nb078AlphaDummy378 g)), ((nb078AlphaDummy368),
        (nb078AlphaDummy370 g)), ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)), ((nb078AlphaDummy571),
        (nb078AlphaDummy574 g)), ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)), ((nb078AlphaDummy575),
        (nb078AlphaDummy576 g)), ((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
        ((nb078AlphaDummy565), (nb078AlphaDummy566 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy381))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy383
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy388) ≠
        (nb078AlphaDummy399) from (by
          unfold
            nb078AlphaDummy399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0396)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy400 g) from (by
          unfold
            nb078AlphaDummy400;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0397
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy397)
        from (by
          unfold
            nb078AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0394)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy398 g) from (by
          unfold
            nb078AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0395
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy399)
        from (by
          unfold
            nb078AlphaDummy399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0396)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy400 g) from (by
          unfold
            nb078AlphaDummy400;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0397
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy397)
        from (by
          unfold
            nb078AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0394)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy398 g) from (by
          unfold
            nb078AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0395
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy401) from (by
          unfold
            nb078AlphaDummy401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0400)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy402 g) from (by
          unfold
            nb078AlphaDummy402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0401
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy397)
        from (by
          unfold
            nb078AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0398)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy398 g) from (by
          unfold
            nb078AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0399
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy389) ≠
        (nb078AlphaDummy401) from (by
          unfold
            nb078AlphaDummy401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0400)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy402 g) from (by
          unfold
            nb078AlphaDummy402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0401
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy397)
        from (by
          unfold
            nb078AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0398)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy398 g) from (by
          unfold
            nb078AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0399
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy381) ≠ (nb078AlphaDummy385) from
                                        (by
                                          unfold nb078AlphaDummy385;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0382)
                                                  0)))) (show (nb078AlphaDummy383 g) ≠
        (nb078AlphaDummy386 g) from (by
                                          unfold nb078AlphaDummy386;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0383 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy385), (nb078AlphaDummy386 g)),
                                      ((nb078AlphaDummy381), (nb078AlphaDummy383 g)),
                                      ((nb078AlphaDummy382), (nb078AlphaDummy384 g)),
                                      ((nb078AlphaDummy374), (nb078AlphaDummy376 g)),
                                      ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
                                      ((nb078AlphaDummy379), (nb078AlphaDummy380 g)),
                                      ((nb078AlphaDummy377), (nb078AlphaDummy378 g)),
                                      ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
                                      ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
                                      ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
                                      ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                                      ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                                      ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                                      ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                                      ((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
                                      ((nb078AlphaDummy565), (nb078AlphaDummy566 g)),
                                      ((nb078AlphaDummy001), g),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy381) ≠ (nb078AlphaDummy385) from (by
                                        unfold nb078AlphaDummy385;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0382)
                                                0)))) (show (nb078AlphaDummy383 g) ≠
                                        (nb078AlphaDummy386 g) from (by
                                        unfold nb078AlphaDummy386;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0383 g)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy381) ≠ (nb078AlphaDummy385) from
                                        (by
                                          unfold nb078AlphaDummy385;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0382)
                                                  0)))) (show (nb078AlphaDummy383 g) ≠
        (nb078AlphaDummy386 g) from (by
                                          unfold nb078AlphaDummy386;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0383 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy385), (nb078AlphaDummy386 g)),
                                      ((nb078AlphaDummy381), (nb078AlphaDummy383 g)),
                                      ((nb078AlphaDummy382), (nb078AlphaDummy384 g)),
                                      ((nb078AlphaDummy374), (nb078AlphaDummy376 g)),
                                      ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
                                      ((nb078AlphaDummy379), (nb078AlphaDummy380 g)),
                                      ((nb078AlphaDummy377), (nb078AlphaDummy378 g)),
                                      ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
                                      ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
                                      ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
                                      ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                                      ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                                      ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                                      ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                                      ((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
                                      ((nb078AlphaDummy565), (nb078AlphaDummy566 g)),
                                      ((nb078AlphaDummy001), g),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part104`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0078`. -/
@[expose]
noncomputable def nb078SplitAlpha0078 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078AlphaDummy407), (nb078AlphaDummy408 g)),
        ((nb078AlphaDummy405), (nb078AlphaDummy406 g)),
        ((nb078AlphaDummy374), (nb078AlphaDummy376 g)),
        ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
        ((nb078AlphaDummy403), (nb078AlphaDummy404 g)),
        ((nb078AlphaDummy377), (nb078AlphaDummy378 g)),
        ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
        ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
        ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
        ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
        ((nb078AlphaDummy565), (nb078AlphaDummy566 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy407))
          (synCphi (Class.cv (nb078AlphaDummy374)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy407))
            (synCphi (Class.cv (nb078AlphaDummy374))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy408 g))
          (synCphi (Class.cv (nb078AlphaDummy376 g)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy408 g))
            (synCphi (Class.cv (nb078AlphaDummy376 g)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy374) ≠ (nb078AlphaDummy381) from
                    (by
                      unfold nb078AlphaDummy381;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0380) 0))))
                  (show (nb078AlphaDummy376 g) ≠ (nb078AlphaDummy383 g) from (by
                      unfold nb078AlphaDummy383;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0381 g) 0))))
                  (TAlphaVar.there (show (nb078AlphaDummy374) ≠ (nb078AlphaDummy382) from
                      (by
                        unfold nb078AlphaDummy382;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0380) 1))))
                    (show (nb078AlphaDummy376 g) ≠ (nb078AlphaDummy384 g) from (by
                        unfold nb078AlphaDummy384;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0381 g) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy374) ≠ (nb078AlphaDummy407) from (by
                          unfold nb078AlphaDummy407;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0410) 0))))
                      (show (nb078AlphaDummy376 g) ≠ (nb078AlphaDummy408 g) from (by
                          unfold nb078AlphaDummy408;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0411 g) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy374) ≠ (nb078AlphaDummy405) from (by
                            unfold nb078AlphaDummy405;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0408) 0))))
                        (show (nb078AlphaDummy376 g) ≠ (nb078AlphaDummy406 g) from (by
                            unfold nb078AlphaDummy406;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0409 g) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy374))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy376 g))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy381) ≠ (nb078AlphaDummy388) from (by
                                        unfold nb078AlphaDummy388;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0384)
                                                1)))) (show (nb078AlphaDummy383 g) ≠
                                        (nb078AlphaDummy391 g) from (by
                                        unfold nb078AlphaDummy391;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0385 g)
                                                1)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy381) ≠ (nb078AlphaDummy387) from
                                        (by
                                          unfold nb078AlphaDummy387;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0384)
                                                  0)))) (show (nb078AlphaDummy383 g) ≠
        (nb078AlphaDummy390 g) from (by
                                          unfold nb078AlphaDummy390;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0385 g) 0))))
                                      (TAlphaVar.there (show (nb078AlphaDummy381) ≠
        (nb078AlphaDummy385) from (by
          unfold nb078AlphaDummy385;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0382) 0)))) (show (nb078AlphaDummy383 g) ≠
        (nb078AlphaDummy386 g) from (by
          unfold nb078AlphaDummy386;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0383 g) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb078AlphaDummy389),
        (nb078AlphaDummy392 g)), ((nb078AlphaDummy388), (nb078AlphaDummy391 g)),
                                        ((nb078AlphaDummy387), (nb078AlphaDummy390 g)),
                                        ((nb078AlphaDummy385), (nb078AlphaDummy386 g)),
                                        ((nb078AlphaDummy381), (nb078AlphaDummy383 g)),
                                        ((nb078AlphaDummy382), (nb078AlphaDummy384 g)),
                                        ((nb078AlphaDummy407), (nb078AlphaDummy408 g)),
                                        ((nb078AlphaDummy405), (nb078AlphaDummy406 g)),
                                        ((nb078AlphaDummy374), (nb078AlphaDummy376 g)),
                                        ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
                                        ((nb078AlphaDummy403), (nb078AlphaDummy404 g)),
                                        ((nb078AlphaDummy377), (nb078AlphaDummy378 g)),
                                        ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
                                        ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
                                        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
                                        ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                                        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                                        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                                        ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                                        ((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
                                        ((nb078AlphaDummy565), (nb078AlphaDummy566 g)),
                                        ((nb078AlphaDummy001), g),
                                        ((nb078AlphaDummy004), y),
                                        ((nb078AlphaDummy003), x)]
                                      (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy388) ≠
        (nb078AlphaDummy395) from (by
          unfold
            nb078AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0388)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy396 g) from (by
          unfold
            nb078AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0389
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy393)
        from (by
          unfold
            nb078AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0386)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy394 g) from (by
          unfold
            nb078AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0387
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy395)
        from (by
          unfold
            nb078AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0392)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy396 g) from (by
          unfold
            nb078AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0393
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy393)
        from (by
          unfold
            nb078AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0390)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy394 g) from (by
          unfold
            nb078AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0391
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy395) from (by
          unfold
            nb078AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0388)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy396 g) from (by
          unfold
            nb078AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0389
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy393)
        from (by
          unfold
            nb078AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0386)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy394 g) from (by
          unfold
            nb078AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0387
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy395)
        from (by
          unfold
            nb078AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0392)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy396 g) from (by
          unfold
            nb078AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0393
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy393)
        from (by
          unfold
            nb078AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0390)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy394 g) from (by
          unfold
            nb078AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0391
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb078AlphaDummy389), (nb078AlphaDummy392 g)),
        ((nb078AlphaDummy388), (nb078AlphaDummy391 g)), ((nb078AlphaDummy387),
        (nb078AlphaDummy390 g)), ((nb078AlphaDummy385), (nb078AlphaDummy386 g)),
        ((nb078AlphaDummy381), (nb078AlphaDummy383 g)), ((nb078AlphaDummy382),
        (nb078AlphaDummy384 g)), ((nb078AlphaDummy407), (nb078AlphaDummy408 g)),
        ((nb078AlphaDummy405), (nb078AlphaDummy406 g)), ((nb078AlphaDummy374),
        (nb078AlphaDummy376 g)), ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
        ((nb078AlphaDummy403), (nb078AlphaDummy404 g)), ((nb078AlphaDummy377),
        (nb078AlphaDummy378 g)), ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
        ((nb078AlphaDummy367), (nb078AlphaDummy369 g)), ((nb078AlphaDummy371),
        (nb078AlphaDummy372 g)), ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)), ((nb078AlphaDummy569),
        (nb078AlphaDummy572 g)), ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy567), (nb078AlphaDummy568 g)), ((nb078AlphaDummy565),
        (nb078AlphaDummy566 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy388) ≠
        (nb078AlphaDummy399) from (by
          unfold
            nb078AlphaDummy399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0396)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy400 g) from (by
          unfold
            nb078AlphaDummy400;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0397
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy397)
        from (by
          unfold
            nb078AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0394)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy398 g) from (by
          unfold
            nb078AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0395
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy399)
        from (by
          unfold
            nb078AlphaDummy399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0396)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy400 g) from (by
          unfold
            nb078AlphaDummy400;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0397
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy397)
        from (by
          unfold
            nb078AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0394)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy398 g) from (by
          unfold
            nb078AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0395
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy401) from (by
          unfold
            nb078AlphaDummy401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0400)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy402 g) from (by
          unfold
            nb078AlphaDummy402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0401
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy397)
        from (by
          unfold
            nb078AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0398)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy398 g) from (by
          unfold
            nb078AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0399
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy389) ≠
        (nb078AlphaDummy401) from (by
          unfold
            nb078AlphaDummy401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0400)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy402 g) from (by
          unfold
            nb078AlphaDummy402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0401
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy397)
        from (by
          unfold
            nb078AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0398)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy398 g) from (by
          unfold
            nb078AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0399
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy381) ≠ (nb078AlphaDummy385) from (by
                                unfold nb078AlphaDummy385;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0382) 0))))
                            (show (nb078AlphaDummy383 g) ≠ (nb078AlphaDummy386 g) from (by
                                unfold nb078AlphaDummy386;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0383 g) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb078AlphaDummy385), (nb078AlphaDummy386 g)),
                            ((nb078AlphaDummy381), (nb078AlphaDummy383 g)),
                            ((nb078AlphaDummy382), (nb078AlphaDummy384 g)),
                            ((nb078AlphaDummy407), (nb078AlphaDummy408 g)),
                            ((nb078AlphaDummy405), (nb078AlphaDummy406 g)),
                            ((nb078AlphaDummy374), (nb078AlphaDummy376 g)),
                            ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
                            ((nb078AlphaDummy403), (nb078AlphaDummy404 g)),
                            ((nb078AlphaDummy377), (nb078AlphaDummy378 g)),
                            ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
                            ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
                            ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
                            ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                            ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                            ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                            ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                            ((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
                            ((nb078AlphaDummy565), (nb078AlphaDummy566 g)),
                            ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                            ((nb078AlphaDummy003), x)]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy381) ≠ (nb078AlphaDummy385) from (by
                              unfold nb078AlphaDummy385;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0382) 0))))
                          (show (nb078AlphaDummy383 g) ≠ (nb078AlphaDummy386 g) from (by
                              unfold nb078AlphaDummy386;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0383 g) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy381) ≠ (nb078AlphaDummy385) from (by
                                unfold nb078AlphaDummy385;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0382) 0))))
                            (show (nb078AlphaDummy383 g) ≠ (nb078AlphaDummy386 g) from (by
                                unfold nb078AlphaDummy386;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0383 g) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb078AlphaDummy385), (nb078AlphaDummy386 g)),
                            ((nb078AlphaDummy381), (nb078AlphaDummy383 g)),
                            ((nb078AlphaDummy382), (nb078AlphaDummy384 g)),
                            ((nb078AlphaDummy407), (nb078AlphaDummy408 g)),
                            ((nb078AlphaDummy405), (nb078AlphaDummy406 g)),
                            ((nb078AlphaDummy374), (nb078AlphaDummy376 g)),
                            ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
                            ((nb078AlphaDummy403), (nb078AlphaDummy404 g)),
                            ((nb078AlphaDummy377), (nb078AlphaDummy378 g)),
                            ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
                            ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
                            ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
                            ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                            ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                            ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                            ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                            ((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
                            ((nb078AlphaDummy565), (nb078AlphaDummy566 g)),
                            ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                            ((nb078AlphaDummy003), x)]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb078AlphaDummy374) ≠ (nb078AlphaDummy381) from (by
                        unfold nb078AlphaDummy381;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0380) 0))))
                    (show (nb078AlphaDummy376 g) ≠ (nb078AlphaDummy383 g) from (by
                        unfold nb078AlphaDummy383;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0381 g) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy374) ≠ (nb078AlphaDummy382) from (by
                          unfold nb078AlphaDummy382;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0380) 1))))
                      (show (nb078AlphaDummy376 g) ≠ (nb078AlphaDummy384 g) from (by
                          unfold nb078AlphaDummy384;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0381 g) 1))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy374) ≠ (nb078AlphaDummy407) from (by
                            unfold nb078AlphaDummy407;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0410) 0))))
                        (show (nb078AlphaDummy376 g) ≠ (nb078AlphaDummy408 g) from (by
                            unfold nb078AlphaDummy408;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0411 g) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy374) ≠ (nb078AlphaDummy405) from (by
                              unfold nb078AlphaDummy405;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0408) 0))))
                          (show (nb078AlphaDummy376 g) ≠ (nb078AlphaDummy406 g) from (by
                              unfold nb078AlphaDummy406;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0409 g) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy374))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy376 g))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb078AlphaDummy381) ≠ (nb078AlphaDummy388) from
                                        (by
                                          unfold nb078AlphaDummy388;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0384)
                                                  1)))) (show (nb078AlphaDummy383 g) ≠
        (nb078AlphaDummy391 g) from (by
                                          unfold nb078AlphaDummy391;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0385 g) 1))))
                                      (TAlphaVar.there (show (nb078AlphaDummy381) ≠
        (nb078AlphaDummy387) from (by
          unfold nb078AlphaDummy387;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0384) 0)))) (show (nb078AlphaDummy383 g) ≠
        (nb078AlphaDummy390 g) from (by
          unfold nb078AlphaDummy390;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0385 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy381) ≠ (nb078AlphaDummy385) from (by
          unfold nb078AlphaDummy385;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0382) 0)))) (show (nb078AlphaDummy383 g) ≠
        (nb078AlphaDummy386 g) from (by
          unfold nb078AlphaDummy386;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0383 g) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb078AlphaDummy389),
        (nb078AlphaDummy392 g)), ((nb078AlphaDummy388), (nb078AlphaDummy391 g)),
        ((nb078AlphaDummy387), (nb078AlphaDummy390 g)), ((nb078AlphaDummy385),
        (nb078AlphaDummy386 g)), ((nb078AlphaDummy381), (nb078AlphaDummy383 g)),
        ((nb078AlphaDummy382), (nb078AlphaDummy384 g)), ((nb078AlphaDummy407),
        (nb078AlphaDummy408 g)), ((nb078AlphaDummy405), (nb078AlphaDummy406 g)),
        ((nb078AlphaDummy374), (nb078AlphaDummy376 g)), ((nb078AlphaDummy373),
        (nb078AlphaDummy375 g)), ((nb078AlphaDummy403), (nb078AlphaDummy404 g)),
        ((nb078AlphaDummy377), (nb078AlphaDummy378 g)), ((nb078AlphaDummy368),
        (nb078AlphaDummy370 g)), ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)), ((nb078AlphaDummy571),
        (nb078AlphaDummy574 g)), ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)), ((nb078AlphaDummy575),
        (nb078AlphaDummy576 g)), ((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
        ((nb078AlphaDummy565), (nb078AlphaDummy566 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
                                        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy388) ≠
        (nb078AlphaDummy395) from (by
          unfold
            nb078AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0388)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy396 g) from (by
          unfold
            nb078AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0389
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy393)
        from (by
          unfold
            nb078AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0386)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy394 g) from (by
          unfold
            nb078AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0387
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy395)
        from (by
          unfold
            nb078AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0392)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy396 g) from (by
          unfold
            nb078AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0393
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy393)
        from (by
          unfold
            nb078AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0390)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy394 g) from (by
          unfold
            nb078AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0391
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy395) from (by
          unfold
            nb078AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0388)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy396 g) from (by
          unfold
            nb078AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0389
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy393)
        from (by
          unfold
            nb078AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0386)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy394 g) from (by
          unfold
            nb078AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0387
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy395)
        from (by
          unfold
            nb078AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0392)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy396 g) from (by
          unfold
            nb078AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0393
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy393)
        from (by
          unfold
            nb078AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0390)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy394 g) from (by
          unfold
            nb078AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0391
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy389), (nb078AlphaDummy392 g)), ((nb078AlphaDummy388),
        (nb078AlphaDummy391 g)), ((nb078AlphaDummy387), (nb078AlphaDummy390 g)),
        ((nb078AlphaDummy385), (nb078AlphaDummy386 g)), ((nb078AlphaDummy381),
        (nb078AlphaDummy383 g)), ((nb078AlphaDummy382), (nb078AlphaDummy384 g)),
        ((nb078AlphaDummy407), (nb078AlphaDummy408 g)), ((nb078AlphaDummy405),
        (nb078AlphaDummy406 g)), ((nb078AlphaDummy374), (nb078AlphaDummy376 g)),
        ((nb078AlphaDummy373), (nb078AlphaDummy375 g)), ((nb078AlphaDummy403),
        (nb078AlphaDummy404 g)), ((nb078AlphaDummy377), (nb078AlphaDummy378 g)),
        ((nb078AlphaDummy368), (nb078AlphaDummy370 g)), ((nb078AlphaDummy367),
        (nb078AlphaDummy369 g)), ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
        ((nb078AlphaDummy571), (nb078AlphaDummy574 g)), ((nb078AlphaDummy570),
        (nb078AlphaDummy573 g)), ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
        ((nb078AlphaDummy575), (nb078AlphaDummy576 g)), ((nb078AlphaDummy567),
        (nb078AlphaDummy568 g)), ((nb078AlphaDummy565), (nb078AlphaDummy566 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy388) ≠
        (nb078AlphaDummy399) from (by
          unfold
            nb078AlphaDummy399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0396)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy400 g) from (by
          unfold
            nb078AlphaDummy400;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0397
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy397)
        from (by
          unfold
            nb078AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0394)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy398 g) from (by
          unfold
            nb078AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0395
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy399)
        from (by
          unfold
            nb078AlphaDummy399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0396)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy400 g) from (by
          unfold
            nb078AlphaDummy400;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0397
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy397)
        from (by
          unfold
            nb078AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0394)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy398 g) from (by
          unfold
            nb078AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0395
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy401) from (by
          unfold
            nb078AlphaDummy401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0400)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy402 g) from (by
          unfold
            nb078AlphaDummy402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0401
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy397)
        from (by
          unfold
            nb078AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0398)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy398 g) from (by
          unfold
            nb078AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0399
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy389) ≠
        (nb078AlphaDummy401) from (by
          unfold
            nb078AlphaDummy401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0400)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy402 g) from (by
          unfold
            nb078AlphaDummy402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0401
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy397)
        from (by
          unfold
            nb078AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0398)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy398 g) from (by
          unfold
            nb078AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0399
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078AlphaDummy381) ≠ (nb078AlphaDummy385) from (by
                                  unfold nb078AlphaDummy385;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0382) 0))))
                              (show (nb078AlphaDummy383 g) ≠ (nb078AlphaDummy386 g) from
                                (by
                                  unfold nb078AlphaDummy386;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0383 g) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb078AlphaDummy385), (nb078AlphaDummy386 g)),
                              ((nb078AlphaDummy381), (nb078AlphaDummy383 g)),
                              ((nb078AlphaDummy382), (nb078AlphaDummy384 g)),
                              ((nb078AlphaDummy407), (nb078AlphaDummy408 g)),
                              ((nb078AlphaDummy405), (nb078AlphaDummy406 g)),
                              ((nb078AlphaDummy374), (nb078AlphaDummy376 g)),
                              ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
                              ((nb078AlphaDummy403), (nb078AlphaDummy404 g)),
                              ((nb078AlphaDummy377), (nb078AlphaDummy378 g)),
                              ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
                              ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
                              ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
                              ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                              ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                              ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                              ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                              ((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
                              ((nb078AlphaDummy565), (nb078AlphaDummy566 g)),
                              ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                              ((nb078AlphaDummy003), x)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy381) ≠ (nb078AlphaDummy385) from (by
                                unfold nb078AlphaDummy385;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0382) 0))))
                            (show (nb078AlphaDummy383 g) ≠ (nb078AlphaDummy386 g) from (by
                                unfold nb078AlphaDummy386;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0383 g) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078AlphaDummy381) ≠ (nb078AlphaDummy385) from (by
                                  unfold nb078AlphaDummy385;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0382) 0))))
                              (show (nb078AlphaDummy383 g) ≠ (nb078AlphaDummy386 g) from
                                (by
                                  unfold nb078AlphaDummy386;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0383 g) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb078AlphaDummy385), (nb078AlphaDummy386 g)),
                              ((nb078AlphaDummy381), (nb078AlphaDummy383 g)),
                              ((nb078AlphaDummy382), (nb078AlphaDummy384 g)),
                              ((nb078AlphaDummy407), (nb078AlphaDummy408 g)),
                              ((nb078AlphaDummy405), (nb078AlphaDummy406 g)),
                              ((nb078AlphaDummy374), (nb078AlphaDummy376 g)),
                              ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
                              ((nb078AlphaDummy403), (nb078AlphaDummy404 g)),
                              ((nb078AlphaDummy377), (nb078AlphaDummy378 g)),
                              ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
                              ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
                              ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
                              ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                              ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                              ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                              ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                              ((nb078AlphaDummy567), (nb078AlphaDummy568 g)),
                              ((nb078AlphaDummy565), (nb078AlphaDummy566 g)),
                              ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                              ((nb078AlphaDummy003), x)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
