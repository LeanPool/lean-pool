/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block035

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part110`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0085`. -/
@[expose]
noncomputable def nb078SplitAlpha0085 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078AlphaDummy645), (nb078AlphaDummy646 g)),
        ((nb078AlphaDummy614), (nb078AlphaDummy616 g)),
        ((nb078AlphaDummy613), (nb078AlphaDummy615 g)),
        ((nb078AlphaDummy643), (nb078AlphaDummy644 g)),
        ((nb078AlphaDummy617), (nb078AlphaDummy618 g)),
        ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
        ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.neg (synWa (Wff.classMem (Class.cv (nb078AlphaDummy645))
            (synCcompl (synCphi (Class.cv (nb078AlphaDummy614)))))
          (Wff.classMem (Class.cv (nb078AlphaDummy645)) (synCcompl (synCsn (synC0c))))))
      (Wff.neg (synWa (Wff.classMem (Class.cv (nb078AlphaDummy646 g))
            (synCcompl (synCphi (Class.cv (nb078AlphaDummy616 g)))))
          (Wff.classMem (Class.cv (nb078AlphaDummy646 g))
            (synCcompl (synCsn (synC0c)))))) :=
  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy614) ≠ (nb078AlphaDummy621) from (by
                                unfold nb078AlphaDummy621;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0636) 0))))
                            (show (nb078AlphaDummy616 g) ≠ (nb078AlphaDummy623 g) from (by
                                unfold nb078AlphaDummy623;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0637 g) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy614) ≠ (nb078AlphaDummy622) from (by
                                  unfold nb078AlphaDummy622;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0636) 1))))
                              (show (nb078AlphaDummy616 g) ≠ (nb078AlphaDummy624 g) from
                                (by
                                  unfold nb078AlphaDummy624;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0637 g) 1))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy614) ≠ (nb078AlphaDummy647) from (by
                                    unfold nb078AlphaDummy647;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0666) 0)))) (show
                                  (nb078AlphaDummy616 g) ≠ (nb078AlphaDummy648 g) from (by
                                    unfold nb078AlphaDummy648;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0667 g)
                                            0)))) (TAlphaVar.there
                                  (show (nb078AlphaDummy614) ≠ (nb078AlphaDummy645) from
                                    (by
                                      unfold nb078AlphaDummy645;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0664)
                                              0)))) (show
                                    (nb078AlphaDummy616 g) ≠ (nb078AlphaDummy646 g) from
                                    (by
                                      unfold nb078AlphaDummy646;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0665 g)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy614))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy616 g))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy621) ≠ (nb078AlphaDummy628) from (by
          unfold nb078AlphaDummy628;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0640) 1)))) (show (nb078AlphaDummy623 g) ≠
        (nb078AlphaDummy631 g) from (by
          unfold nb078AlphaDummy631;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0641 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy621) ≠ (nb078AlphaDummy627) from (by
          unfold nb078AlphaDummy627;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0640) 0)))) (show (nb078AlphaDummy623 g) ≠
        (nb078AlphaDummy630 g) from (by
          unfold nb078AlphaDummy630;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0641 g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy621) ≠ (nb078AlphaDummy625)
        from (by
          unfold nb078AlphaDummy625;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0638)
                  0)))) (show (nb078AlphaDummy623 g) ≠ (nb078AlphaDummy626 g) from (by
          unfold nb078AlphaDummy626;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0639 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy629), (nb078AlphaDummy632 g)), ((nb078AlphaDummy628),
        (nb078AlphaDummy631 g)), ((nb078AlphaDummy627), (nb078AlphaDummy630 g)),
        ((nb078AlphaDummy625), (nb078AlphaDummy626 g)), ((nb078AlphaDummy621),
        (nb078AlphaDummy623 g)), ((nb078AlphaDummy622), (nb078AlphaDummy624 g)),
        ((nb078AlphaDummy647), (nb078AlphaDummy648 g)), ((nb078AlphaDummy645),
        (nb078AlphaDummy646 g)), ((nb078AlphaDummy614), (nb078AlphaDummy616 g)),
        ((nb078AlphaDummy613), (nb078AlphaDummy615 g)), ((nb078AlphaDummy643),
        (nb078AlphaDummy644 g)), ((nb078AlphaDummy617), (nb078AlphaDummy618 g)),
        ((nb078AlphaDummy571), (nb078AlphaDummy574 g)), ((nb078AlphaDummy570),
        (nb078AlphaDummy573 g)), ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
        ((nb078AlphaDummy575), (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy628) ≠ (nb078AlphaDummy635) from (by
          unfold
            nb078AlphaDummy635;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0644)
                  0)))) (show (nb078AlphaDummy631 g) ≠ (nb078AlphaDummy636 g) from (by
          unfold
            nb078AlphaDummy636;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0645
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy628) ≠ (nb078AlphaDummy633)
        from (by
          unfold
            nb078AlphaDummy633;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0642)
                  0)))) (show (nb078AlphaDummy631 g) ≠ (nb078AlphaDummy634 g) from (by
          unfold
            nb078AlphaDummy634;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0643
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy621))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy623 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy629) ≠ (nb078AlphaDummy635)
        from (by
          unfold
            nb078AlphaDummy635;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0648)
                  0)))) (show (nb078AlphaDummy632 g) ≠ (nb078AlphaDummy636 g) from (by
          unfold
            nb078AlphaDummy636;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0649
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy629) ≠ (nb078AlphaDummy633)
        from (by
          unfold
            nb078AlphaDummy633;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0646)
                  0)))) (show (nb078AlphaDummy632 g) ≠ (nb078AlphaDummy634 g) from (by
          unfold
            nb078AlphaDummy634;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0647
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy628) ≠ (nb078AlphaDummy635) from (by
          unfold
            nb078AlphaDummy635;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0644)
                  0)))) (show (nb078AlphaDummy631 g) ≠ (nb078AlphaDummy636 g) from (by
          unfold
            nb078AlphaDummy636;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0645
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy628) ≠ (nb078AlphaDummy633)
        from (by
          unfold
            nb078AlphaDummy633;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0642)
                  0)))) (show (nb078AlphaDummy631 g) ≠ (nb078AlphaDummy634 g) from (by
          unfold
            nb078AlphaDummy634;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0643
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy621))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy623 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy629) ≠ (nb078AlphaDummy635)
        from (by
          unfold
            nb078AlphaDummy635;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0648)
                  0)))) (show (nb078AlphaDummy632 g) ≠ (nb078AlphaDummy636 g) from (by
          unfold
            nb078AlphaDummy636;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0649
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy629) ≠ (nb078AlphaDummy633)
        from (by
          unfold
            nb078AlphaDummy633;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0646)
                  0)))) (show (nb078AlphaDummy632 g) ≠ (nb078AlphaDummy634 g) from (by
          unfold
            nb078AlphaDummy634;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0647
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy629), (nb078AlphaDummy632 g)), ((nb078AlphaDummy628),
        (nb078AlphaDummy631 g)), ((nb078AlphaDummy627), (nb078AlphaDummy630 g)),
        ((nb078AlphaDummy625), (nb078AlphaDummy626 g)), ((nb078AlphaDummy621),
        (nb078AlphaDummy623 g)), ((nb078AlphaDummy622), (nb078AlphaDummy624 g)),
        ((nb078AlphaDummy647), (nb078AlphaDummy648 g)), ((nb078AlphaDummy645),
        (nb078AlphaDummy646 g)), ((nb078AlphaDummy614), (nb078AlphaDummy616 g)),
        ((nb078AlphaDummy613), (nb078AlphaDummy615 g)), ((nb078AlphaDummy643),
        (nb078AlphaDummy644 g)), ((nb078AlphaDummy617), (nb078AlphaDummy618 g)),
        ((nb078AlphaDummy571), (nb078AlphaDummy574 g)), ((nb078AlphaDummy570),
        (nb078AlphaDummy573 g)), ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
        ((nb078AlphaDummy575), (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy621))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy623
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy621))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy623 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy628) ≠
        (nb078AlphaDummy639) from (by
          unfold
            nb078AlphaDummy639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0652)
                  0)))) (show (nb078AlphaDummy631 g) ≠ (nb078AlphaDummy640 g) from (by
          unfold
            nb078AlphaDummy640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0653
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy628) ≠ (nb078AlphaDummy637)
        from (by
          unfold
            nb078AlphaDummy637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0650)
                  0)))) (show (nb078AlphaDummy631 g) ≠ (nb078AlphaDummy638 g) from (by
          unfold
            nb078AlphaDummy638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0651
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy621))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy623 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy628) ≠ (nb078AlphaDummy639)
        from (by
          unfold
            nb078AlphaDummy639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0652)
                  0)))) (show (nb078AlphaDummy631 g) ≠ (nb078AlphaDummy640 g) from (by
          unfold
            nb078AlphaDummy640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0653
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy628) ≠ (nb078AlphaDummy637)
        from (by
          unfold
            nb078AlphaDummy637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0650)
                  0)))) (show (nb078AlphaDummy631 g) ≠ (nb078AlphaDummy638 g) from (by
          unfold
            nb078AlphaDummy638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0651
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy621))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy623 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy629) ≠ (nb078AlphaDummy641) from (by
          unfold
            nb078AlphaDummy641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0656)
                  0)))) (show (nb078AlphaDummy632 g) ≠ (nb078AlphaDummy642 g) from (by
          unfold
            nb078AlphaDummy642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0657
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy629) ≠ (nb078AlphaDummy637)
        from (by
          unfold
            nb078AlphaDummy637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0654)
                  0)))) (show (nb078AlphaDummy632 g) ≠ (nb078AlphaDummy638 g) from (by
          unfold
            nb078AlphaDummy638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0655
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy629) ≠
        (nb078AlphaDummy641) from (by
          unfold
            nb078AlphaDummy641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0656)
                  0)))) (show (nb078AlphaDummy632 g) ≠ (nb078AlphaDummy642 g) from (by
          unfold
            nb078AlphaDummy642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0657
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy629) ≠ (nb078AlphaDummy637)
        from (by
          unfold
            nb078AlphaDummy637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0654)
                  0)))) (show (nb078AlphaDummy632 g) ≠ (nb078AlphaDummy638 g) from (by
          unfold
            nb078AlphaDummy638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0655
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy621) ≠ (nb078AlphaDummy625) from
                                        (by
                                          unfold nb078AlphaDummy625;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0638)
                                                  0)))) (show (nb078AlphaDummy623 g) ≠
        (nb078AlphaDummy626 g) from (by
                                          unfold nb078AlphaDummy626;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0639 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy625), (nb078AlphaDummy626 g)),
                                      ((nb078AlphaDummy621), (nb078AlphaDummy623 g)),
                                      ((nb078AlphaDummy622), (nb078AlphaDummy624 g)),
                                      ((nb078AlphaDummy647), (nb078AlphaDummy648 g)),
                                      ((nb078AlphaDummy645), (nb078AlphaDummy646 g)),
                                      ((nb078AlphaDummy614), (nb078AlphaDummy616 g)),
                                      ((nb078AlphaDummy613), (nb078AlphaDummy615 g)),
                                      ((nb078AlphaDummy643), (nb078AlphaDummy644 g)),
                                      ((nb078AlphaDummy617), (nb078AlphaDummy618 g)),
                                      ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                                      ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                                      ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                                      ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                                      ((nb078AlphaDummy001), g),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy621) ≠ (nb078AlphaDummy625) from (by
                                        unfold nb078AlphaDummy625;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0638)
                                                0)))) (show (nb078AlphaDummy623 g) ≠
                                        (nb078AlphaDummy626 g) from (by
                                        unfold nb078AlphaDummy626;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0639 g)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy621) ≠ (nb078AlphaDummy625) from
                                        (by
                                          unfold nb078AlphaDummy625;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0638)
                                                  0)))) (show (nb078AlphaDummy623 g) ≠
        (nb078AlphaDummy626 g) from (by
                                          unfold nb078AlphaDummy626;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0639 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy625), (nb078AlphaDummy626 g)),
                                      ((nb078AlphaDummy621), (nb078AlphaDummy623 g)),
                                      ((nb078AlphaDummy622), (nb078AlphaDummy624 g)),
                                      ((nb078AlphaDummy647), (nb078AlphaDummy648 g)),
                                      ((nb078AlphaDummy645), (nb078AlphaDummy646 g)),
                                      ((nb078AlphaDummy614), (nb078AlphaDummy616 g)),
                                      ((nb078AlphaDummy613), (nb078AlphaDummy615 g)),
                                      ((nb078AlphaDummy643), (nb078AlphaDummy644 g)),
                                      ((nb078AlphaDummy617), (nb078AlphaDummy618 g)),
                                      ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                                      ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                                      ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                                      ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                                      ((nb078AlphaDummy001), g),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy614) ≠ (nb078AlphaDummy621) from (by
                                unfold nb078AlphaDummy621;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0636) 0))))
                            (show (nb078AlphaDummy616 g) ≠ (nb078AlphaDummy623 g) from (by
                                unfold nb078AlphaDummy623;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0637 g) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy614) ≠ (nb078AlphaDummy622) from (by
                                  unfold nb078AlphaDummy622;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0636) 1))))
                              (show (nb078AlphaDummy616 g) ≠ (nb078AlphaDummy624 g) from
                                (by
                                  unfold nb078AlphaDummy624;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0637 g) 1))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy614) ≠ (nb078AlphaDummy647) from (by
                                    unfold nb078AlphaDummy647;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0666) 0)))) (show
                                  (nb078AlphaDummy616 g) ≠ (nb078AlphaDummy648 g) from (by
                                    unfold nb078AlphaDummy648;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0667 g)
                                            0)))) (TAlphaVar.there
                                  (show (nb078AlphaDummy614) ≠ (nb078AlphaDummy645) from
                                    (by
                                      unfold nb078AlphaDummy645;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0664)
                                              0)))) (show
                                    (nb078AlphaDummy616 g) ≠ (nb078AlphaDummy646 g) from
                                    (by
                                      unfold nb078AlphaDummy646;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0665 g)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy614))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy616 g))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy621) ≠ (nb078AlphaDummy628) from (by
          unfold nb078AlphaDummy628;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0640) 1)))) (show (nb078AlphaDummy623 g) ≠
        (nb078AlphaDummy631 g) from (by
          unfold nb078AlphaDummy631;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0641 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy621) ≠ (nb078AlphaDummy627) from (by
          unfold nb078AlphaDummy627;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0640) 0)))) (show (nb078AlphaDummy623 g) ≠
        (nb078AlphaDummy630 g) from (by
          unfold nb078AlphaDummy630;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0641 g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy621) ≠ (nb078AlphaDummy625)
        from (by
          unfold nb078AlphaDummy625;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0638)
                  0)))) (show (nb078AlphaDummy623 g) ≠ (nb078AlphaDummy626 g) from (by
          unfold nb078AlphaDummy626;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0639 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy629), (nb078AlphaDummy632 g)), ((nb078AlphaDummy628),
        (nb078AlphaDummy631 g)), ((nb078AlphaDummy627), (nb078AlphaDummy630 g)),
        ((nb078AlphaDummy625), (nb078AlphaDummy626 g)), ((nb078AlphaDummy621),
        (nb078AlphaDummy623 g)), ((nb078AlphaDummy622), (nb078AlphaDummy624 g)),
        ((nb078AlphaDummy647), (nb078AlphaDummy648 g)), ((nb078AlphaDummy645),
        (nb078AlphaDummy646 g)), ((nb078AlphaDummy614), (nb078AlphaDummy616 g)),
        ((nb078AlphaDummy613), (nb078AlphaDummy615 g)), ((nb078AlphaDummy643),
        (nb078AlphaDummy644 g)), ((nb078AlphaDummy617), (nb078AlphaDummy618 g)),
        ((nb078AlphaDummy571), (nb078AlphaDummy574 g)), ((nb078AlphaDummy570),
        (nb078AlphaDummy573 g)), ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
        ((nb078AlphaDummy575), (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy628) ≠ (nb078AlphaDummy635) from (by
          unfold
            nb078AlphaDummy635;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0644)
                  0)))) (show (nb078AlphaDummy631 g) ≠ (nb078AlphaDummy636 g) from (by
          unfold
            nb078AlphaDummy636;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0645
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy628) ≠ (nb078AlphaDummy633)
        from (by
          unfold
            nb078AlphaDummy633;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0642)
                  0)))) (show (nb078AlphaDummy631 g) ≠ (nb078AlphaDummy634 g) from (by
          unfold
            nb078AlphaDummy634;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0643
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy621))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy623 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy629) ≠ (nb078AlphaDummy635)
        from (by
          unfold
            nb078AlphaDummy635;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0648)
                  0)))) (show (nb078AlphaDummy632 g) ≠ (nb078AlphaDummy636 g) from (by
          unfold
            nb078AlphaDummy636;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0649
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy629) ≠ (nb078AlphaDummy633)
        from (by
          unfold
            nb078AlphaDummy633;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0646)
                  0)))) (show (nb078AlphaDummy632 g) ≠ (nb078AlphaDummy634 g) from (by
          unfold
            nb078AlphaDummy634;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0647
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy628) ≠ (nb078AlphaDummy635) from (by
          unfold
            nb078AlphaDummy635;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0644)
                  0)))) (show (nb078AlphaDummy631 g) ≠ (nb078AlphaDummy636 g) from (by
          unfold
            nb078AlphaDummy636;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0645
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy628) ≠ (nb078AlphaDummy633)
        from (by
          unfold
            nb078AlphaDummy633;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0642)
                  0)))) (show (nb078AlphaDummy631 g) ≠ (nb078AlphaDummy634 g) from (by
          unfold
            nb078AlphaDummy634;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0643
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy621))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy623 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy629) ≠ (nb078AlphaDummy635)
        from (by
          unfold
            nb078AlphaDummy635;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0648)
                  0)))) (show (nb078AlphaDummy632 g) ≠ (nb078AlphaDummy636 g) from (by
          unfold
            nb078AlphaDummy636;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0649
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy629) ≠ (nb078AlphaDummy633)
        from (by
          unfold
            nb078AlphaDummy633;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0646)
                  0)))) (show (nb078AlphaDummy632 g) ≠ (nb078AlphaDummy634 g) from (by
          unfold
            nb078AlphaDummy634;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0647
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy629), (nb078AlphaDummy632 g)), ((nb078AlphaDummy628),
        (nb078AlphaDummy631 g)), ((nb078AlphaDummy627), (nb078AlphaDummy630 g)),
        ((nb078AlphaDummy625), (nb078AlphaDummy626 g)), ((nb078AlphaDummy621),
        (nb078AlphaDummy623 g)), ((nb078AlphaDummy622), (nb078AlphaDummy624 g)),
        ((nb078AlphaDummy647), (nb078AlphaDummy648 g)), ((nb078AlphaDummy645),
        (nb078AlphaDummy646 g)), ((nb078AlphaDummy614), (nb078AlphaDummy616 g)),
        ((nb078AlphaDummy613), (nb078AlphaDummy615 g)), ((nb078AlphaDummy643),
        (nb078AlphaDummy644 g)), ((nb078AlphaDummy617), (nb078AlphaDummy618 g)),
        ((nb078AlphaDummy571), (nb078AlphaDummy574 g)), ((nb078AlphaDummy570),
        (nb078AlphaDummy573 g)), ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
        ((nb078AlphaDummy575), (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy621))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy623
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy621))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy623 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy628) ≠
        (nb078AlphaDummy639) from (by
          unfold
            nb078AlphaDummy639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0652)
                  0)))) (show (nb078AlphaDummy631 g) ≠ (nb078AlphaDummy640 g) from (by
          unfold
            nb078AlphaDummy640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0653
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy628) ≠ (nb078AlphaDummy637)
        from (by
          unfold
            nb078AlphaDummy637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0650)
                  0)))) (show (nb078AlphaDummy631 g) ≠ (nb078AlphaDummy638 g) from (by
          unfold
            nb078AlphaDummy638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0651
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy621))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy623 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy628) ≠ (nb078AlphaDummy639)
        from (by
          unfold
            nb078AlphaDummy639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0652)
                  0)))) (show (nb078AlphaDummy631 g) ≠ (nb078AlphaDummy640 g) from (by
          unfold
            nb078AlphaDummy640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0653
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy628) ≠ (nb078AlphaDummy637)
        from (by
          unfold
            nb078AlphaDummy637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0650)
                  0)))) (show (nb078AlphaDummy631 g) ≠ (nb078AlphaDummy638 g) from (by
          unfold
            nb078AlphaDummy638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0651
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy621))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy623 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy629) ≠ (nb078AlphaDummy641) from (by
          unfold
            nb078AlphaDummy641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0656)
                  0)))) (show (nb078AlphaDummy632 g) ≠ (nb078AlphaDummy642 g) from (by
          unfold
            nb078AlphaDummy642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0657
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy629) ≠ (nb078AlphaDummy637)
        from (by
          unfold
            nb078AlphaDummy637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0654)
                  0)))) (show (nb078AlphaDummy632 g) ≠ (nb078AlphaDummy638 g) from (by
          unfold
            nb078AlphaDummy638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0655
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy629) ≠
        (nb078AlphaDummy641) from (by
          unfold
            nb078AlphaDummy641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0656)
                  0)))) (show (nb078AlphaDummy632 g) ≠ (nb078AlphaDummy642 g) from (by
          unfold
            nb078AlphaDummy642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0657
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy629) ≠ (nb078AlphaDummy637)
        from (by
          unfold
            nb078AlphaDummy637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0654)
                  0)))) (show (nb078AlphaDummy632 g) ≠ (nb078AlphaDummy638 g) from (by
          unfold
            nb078AlphaDummy638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0655
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy621) ≠ (nb078AlphaDummy625) from
                                        (by
                                          unfold nb078AlphaDummy625;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0638)
                                                  0)))) (show (nb078AlphaDummy623 g) ≠
        (nb078AlphaDummy626 g) from (by
                                          unfold nb078AlphaDummy626;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0639 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy625), (nb078AlphaDummy626 g)),
                                      ((nb078AlphaDummy621), (nb078AlphaDummy623 g)),
                                      ((nb078AlphaDummy622), (nb078AlphaDummy624 g)),
                                      ((nb078AlphaDummy647), (nb078AlphaDummy648 g)),
                                      ((nb078AlphaDummy645), (nb078AlphaDummy646 g)),
                                      ((nb078AlphaDummy614), (nb078AlphaDummy616 g)),
                                      ((nb078AlphaDummy613), (nb078AlphaDummy615 g)),
                                      ((nb078AlphaDummy643), (nb078AlphaDummy644 g)),
                                      ((nb078AlphaDummy617), (nb078AlphaDummy618 g)),
                                      ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                                      ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                                      ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                                      ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                                      ((nb078AlphaDummy001), g),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy621) ≠ (nb078AlphaDummy625) from (by
                                        unfold nb078AlphaDummy625;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0638)
                                                0)))) (show (nb078AlphaDummy623 g) ≠
                                        (nb078AlphaDummy626 g) from (by
                                        unfold nb078AlphaDummy626;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0639 g)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy621) ≠ (nb078AlphaDummy625) from
                                        (by
                                          unfold nb078AlphaDummy625;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0638)
                                                  0)))) (show (nb078AlphaDummy623 g) ≠
        (nb078AlphaDummy626 g) from (by
                                          unfold nb078AlphaDummy626;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0639 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy625), (nb078AlphaDummy626 g)),
                                      ((nb078AlphaDummy621), (nb078AlphaDummy623 g)),
                                      ((nb078AlphaDummy622), (nb078AlphaDummy624 g)),
                                      ((nb078AlphaDummy647), (nb078AlphaDummy648 g)),
                                      ((nb078AlphaDummy645), (nb078AlphaDummy646 g)),
                                      ((nb078AlphaDummy614), (nb078AlphaDummy616 g)),
                                      ((nb078AlphaDummy613), (nb078AlphaDummy615 g)),
                                      ((nb078AlphaDummy643), (nb078AlphaDummy644 g)),
                                      ((nb078AlphaDummy617), (nb078AlphaDummy618 g)),
                                      ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                                      ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                                      ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                                      ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                                      ((nb078AlphaDummy001), g),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
          [((nb078AlphaDummy645), (nb078AlphaDummy646 g)),
            ((nb078AlphaDummy614), (nb078AlphaDummy616 g)),
            ((nb078AlphaDummy613), (nb078AlphaDummy615 g)),
            ((nb078AlphaDummy643), (nb078AlphaDummy644 g)),
            ((nb078AlphaDummy617), (nb078AlphaDummy618 g)),
            ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
            ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
            ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
            ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
            ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
            ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part111`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0086`. -/
@[expose]
noncomputable def nb078SplitAlpha0086 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078AlphaDummy661), (nb078AlphaDummy662 g)),
        ((nb078AlphaDummy659), (nb078AlphaDummy660 g)),
        ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
        ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
        ((nb078AlphaDummy653), (nb078AlphaDummy654 g)),
        ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
        ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy661))
          (Class.cab (nb078AlphaDummy655)
            (synWrex (nb078AlphaDummy656) (Class.cv (nb078AlphaDummy649))
              (Wff.classEq (Class.cv (nb078AlphaDummy655))
                (synCphi (Class.cv (nb078AlphaDummy656))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy661)) (Class.cab (nb078AlphaDummy655)
              (synWrex (nb078AlphaDummy656) (Class.cv (nb078AlphaDummy649))
                (Wff.classEq (Class.cv (nb078AlphaDummy655))
                  (synCphi (Class.cv (nb078AlphaDummy656)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy662 g))
          (Class.cab (nb078AlphaDummy657 g)
            (synWrex (nb078AlphaDummy658 g) (Class.cv (nb078AlphaDummy651 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy657 g))
                (synCphi (Class.cv (nb078AlphaDummy658 g))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy662 g))
            (Class.cab (nb078AlphaDummy657 g)
              (synWrex (nb078AlphaDummy658 g) (Class.cv (nb078AlphaDummy651 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy657 g))
                  (synCphi (Class.cv (nb078AlphaDummy658 g))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy649) ≠ (nb078AlphaDummy656) from
                    (by
                      unfold nb078AlphaDummy656;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0672) 1))))
                  (show (nb078AlphaDummy651 g) ≠ (nb078AlphaDummy658 g) from (by
                      unfold nb078AlphaDummy658;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0674 g) 1))))
                  (TAlphaVar.there (show (nb078AlphaDummy649) ≠ (nb078AlphaDummy655) from
                      (by
                        unfold nb078AlphaDummy655;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0672) 0))))
                    (show (nb078AlphaDummy651 g) ≠ (nb078AlphaDummy657 g) from (by
                        unfold nb078AlphaDummy657;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0674 g) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy649) ≠ (nb078AlphaDummy661) from (by
                          unfold nb078AlphaDummy661;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0676) 0))))
                      (show (nb078AlphaDummy651 g) ≠ (nb078AlphaDummy662 g) from (by
                          unfold nb078AlphaDummy662;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0677 g) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy649) ≠ (nb078AlphaDummy659) from (by
                            unfold nb078AlphaDummy659;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0673) 0))))
                        (show (nb078AlphaDummy651 g) ≠ (nb078AlphaDummy660 g) from (by
                            unfold nb078AlphaDummy660;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0675 g) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((synCcnv (Class.cv (nb078AlphaDummy001)))).fv) (by decide))
                          (freshVar_injective (((synCcnv (Class.cv g))).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy649))).fv ∪
                      ((Class.cv (nb078AlphaDummy650))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078AlphaDummy651 g))).fv ∪
                      ((Class.cv (nb078AlphaDummy652 g))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy656) ≠ (nb078AlphaDummy663) from (by
                              unfold nb078AlphaDummy663;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0678) 0))))
                          (show (nb078AlphaDummy658 g) ≠ (nb078AlphaDummy665 g) from (by
                              unfold nb078AlphaDummy665;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0679 g) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy656) ≠ (nb078AlphaDummy664) from (by
                                unfold nb078AlphaDummy664;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0678) 1))))
                            (show (nb078AlphaDummy658 g) ≠ (nb078AlphaDummy666 g) from (by
                                unfold nb078AlphaDummy666;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0679 g) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy656))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy658 g))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy663) ≠ (nb078AlphaDummy670) from (by
          unfold nb078AlphaDummy670;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0682) 1)))) (show (nb078AlphaDummy665 g) ≠
        (nb078AlphaDummy673 g) from (by
          unfold nb078AlphaDummy673;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0683 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy663) ≠ (nb078AlphaDummy669) from (by
          unfold nb078AlphaDummy669;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0682) 0)))) (show (nb078AlphaDummy665 g) ≠
        (nb078AlphaDummy672 g) from (by
          unfold nb078AlphaDummy672;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0683 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy663) ≠ (nb078AlphaDummy667) from (by
          unfold nb078AlphaDummy667;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0680) 0)))) (show (nb078AlphaDummy665 g) ≠
        (nb078AlphaDummy668 g) from (by
          unfold nb078AlphaDummy668;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0681 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy671), (nb078AlphaDummy674 g)), ((nb078AlphaDummy670),
        (nb078AlphaDummy673 g)), ((nb078AlphaDummy669), (nb078AlphaDummy672 g)),
        ((nb078AlphaDummy667), (nb078AlphaDummy668 g)), ((nb078AlphaDummy663),
        (nb078AlphaDummy665 g)), ((nb078AlphaDummy664), (nb078AlphaDummy666 g)),
        ((nb078AlphaDummy656), (nb078AlphaDummy658 g)), ((nb078AlphaDummy655),
        (nb078AlphaDummy657 g)), ((nb078AlphaDummy661), (nb078AlphaDummy662 g)),
        ((nb078AlphaDummy659), (nb078AlphaDummy660 g)), ((nb078AlphaDummy650),
        (nb078AlphaDummy652 g)), ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
        ((nb078AlphaDummy653), (nb078AlphaDummy654 g)), ((nb078AlphaDummy571),
        (nb078AlphaDummy574 g)), ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)), ((nb078AlphaDummy575),
        (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy670) ≠ (nb078AlphaDummy677) from (by
          unfold
            nb078AlphaDummy677;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0686)
                  0)))) (show (nb078AlphaDummy673 g) ≠ (nb078AlphaDummy678 g) from (by
          unfold
            nb078AlphaDummy678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0687
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy670) ≠ (nb078AlphaDummy675)
        from (by
          unfold
            nb078AlphaDummy675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0684)
                  0)))) (show (nb078AlphaDummy673 g) ≠ (nb078AlphaDummy676 g) from (by
          unfold
            nb078AlphaDummy676;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0685
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy663))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy665 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy671) ≠ (nb078AlphaDummy677)
        from (by
          unfold
            nb078AlphaDummy677;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0690)
                  0)))) (show (nb078AlphaDummy674 g) ≠ (nb078AlphaDummy678 g) from (by
          unfold
            nb078AlphaDummy678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0691
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy671) ≠ (nb078AlphaDummy675)
        from (by
          unfold
            nb078AlphaDummy675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0688)
                  0)))) (show (nb078AlphaDummy674 g) ≠ (nb078AlphaDummy676 g) from (by
          unfold
            nb078AlphaDummy676;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0689
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy670) ≠ (nb078AlphaDummy677) from (by
          unfold
            nb078AlphaDummy677;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0686)
                  0)))) (show (nb078AlphaDummy673 g) ≠ (nb078AlphaDummy678 g) from (by
          unfold
            nb078AlphaDummy678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0687
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy670) ≠ (nb078AlphaDummy675)
        from (by
          unfold
            nb078AlphaDummy675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0684)
                  0)))) (show (nb078AlphaDummy673 g) ≠ (nb078AlphaDummy676 g) from (by
          unfold
            nb078AlphaDummy676;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0685
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy663))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy665 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy671) ≠ (nb078AlphaDummy677)
        from (by
          unfold
            nb078AlphaDummy677;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0690)
                  0)))) (show (nb078AlphaDummy674 g) ≠ (nb078AlphaDummy678 g) from (by
          unfold
            nb078AlphaDummy678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0691
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy671) ≠ (nb078AlphaDummy675)
        from (by
          unfold
            nb078AlphaDummy675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0688)
                  0)))) (show (nb078AlphaDummy674 g) ≠ (nb078AlphaDummy676 g) from (by
          unfold
            nb078AlphaDummy676;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0689
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy671), (nb078AlphaDummy674 g)), ((nb078AlphaDummy670),
        (nb078AlphaDummy673 g)), ((nb078AlphaDummy669), (nb078AlphaDummy672 g)),
        ((nb078AlphaDummy667), (nb078AlphaDummy668 g)), ((nb078AlphaDummy663),
        (nb078AlphaDummy665 g)), ((nb078AlphaDummy664), (nb078AlphaDummy666 g)),
        ((nb078AlphaDummy656), (nb078AlphaDummy658 g)), ((nb078AlphaDummy655),
        (nb078AlphaDummy657 g)), ((nb078AlphaDummy661), (nb078AlphaDummy662 g)),
        ((nb078AlphaDummy659), (nb078AlphaDummy660 g)), ((nb078AlphaDummy650),
        (nb078AlphaDummy652 g)), ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
        ((nb078AlphaDummy653), (nb078AlphaDummy654 g)), ((nb078AlphaDummy571),
        (nb078AlphaDummy574 g)), ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)), ((nb078AlphaDummy575),
        (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy663))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy665 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy663))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy665
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy670) ≠ (nb078AlphaDummy681) from (by
          unfold
            nb078AlphaDummy681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0694)
                  0)))) (show (nb078AlphaDummy673 g) ≠ (nb078AlphaDummy682 g) from (by
          unfold
            nb078AlphaDummy682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0695
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy670) ≠ (nb078AlphaDummy679)
        from (by
          unfold
            nb078AlphaDummy679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0692)
                  0)))) (show (nb078AlphaDummy673 g) ≠ (nb078AlphaDummy680 g) from (by
          unfold
            nb078AlphaDummy680;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0693
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy663))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy665 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy670) ≠ (nb078AlphaDummy681)
        from (by
          unfold
            nb078AlphaDummy681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0694)
                  0)))) (show (nb078AlphaDummy673 g) ≠ (nb078AlphaDummy682 g) from (by
          unfold
            nb078AlphaDummy682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0695
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy670) ≠ (nb078AlphaDummy679)
        from (by
          unfold
            nb078AlphaDummy679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0692)
                  0)))) (show (nb078AlphaDummy673 g) ≠ (nb078AlphaDummy680 g) from (by
          unfold
            nb078AlphaDummy680;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0693
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy663))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy665 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy671) ≠ (nb078AlphaDummy683) from (by
          unfold
            nb078AlphaDummy683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0698)
                  0)))) (show (nb078AlphaDummy674 g) ≠ (nb078AlphaDummy684 g) from (by
          unfold
            nb078AlphaDummy684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0699
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy671) ≠ (nb078AlphaDummy679)
        from (by
          unfold
            nb078AlphaDummy679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0696)
                  0)))) (show (nb078AlphaDummy674 g) ≠ (nb078AlphaDummy680 g) from (by
          unfold
            nb078AlphaDummy680;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0697
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy671) ≠
        (nb078AlphaDummy683) from (by
          unfold
            nb078AlphaDummy683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0698)
                  0)))) (show (nb078AlphaDummy674 g) ≠ (nb078AlphaDummy684 g) from (by
          unfold
            nb078AlphaDummy684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0699
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy671) ≠ (nb078AlphaDummy679)
        from (by
          unfold
            nb078AlphaDummy679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0696)
                  0)))) (show (nb078AlphaDummy674 g) ≠ (nb078AlphaDummy680 g) from (by
          unfold
            nb078AlphaDummy680;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0697
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy663) ≠ (nb078AlphaDummy667) from (by
                                        unfold nb078AlphaDummy667;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0680)
                                                0)))) (show (nb078AlphaDummy665 g) ≠
                                        (nb078AlphaDummy668 g) from (by
                                        unfold nb078AlphaDummy668;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0681 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy667), (nb078AlphaDummy668 g)),
                                    ((nb078AlphaDummy663), (nb078AlphaDummy665 g)),
                                    ((nb078AlphaDummy664), (nb078AlphaDummy666 g)),
                                    ((nb078AlphaDummy656), (nb078AlphaDummy658 g)),
                                    ((nb078AlphaDummy655), (nb078AlphaDummy657 g)),
                                    ((nb078AlphaDummy661), (nb078AlphaDummy662 g)),
                                    ((nb078AlphaDummy659), (nb078AlphaDummy660 g)),
                                    ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
                                    ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
                                    ((nb078AlphaDummy653), (nb078AlphaDummy654 g)),
                                    ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                                    ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                                    ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                                    ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                                    ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy663) ≠ (nb078AlphaDummy667) from
                                    (by
                                      unfold nb078AlphaDummy667;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0680)
                                              0)))) (show
                                    (nb078AlphaDummy665 g) ≠ (nb078AlphaDummy668 g) from
                                    (by
                                      unfold nb078AlphaDummy668;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0681 g)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy663) ≠ (nb078AlphaDummy667) from (by
                                        unfold nb078AlphaDummy667;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0680)
                                                0)))) (show (nb078AlphaDummy665 g) ≠
                                        (nb078AlphaDummy668 g) from (by
                                        unfold nb078AlphaDummy668;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0681 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy667), (nb078AlphaDummy668 g)),
                                    ((nb078AlphaDummy663), (nb078AlphaDummy665 g)),
                                    ((nb078AlphaDummy664), (nb078AlphaDummy666 g)),
                                    ((nb078AlphaDummy656), (nb078AlphaDummy658 g)),
                                    ((nb078AlphaDummy655), (nb078AlphaDummy657 g)),
                                    ((nb078AlphaDummy661), (nb078AlphaDummy662 g)),
                                    ((nb078AlphaDummy659), (nb078AlphaDummy660 g)),
                                    ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
                                    ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
                                    ((nb078AlphaDummy653), (nb078AlphaDummy654 g)),
                                    ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                                    ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                                    ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                                    ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                                    ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078AlphaDummy649) ≠ (nb078AlphaDummy656) from
                      (by
                        unfold nb078AlphaDummy656;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0672) 1))))
                    (show (nb078AlphaDummy651 g) ≠ (nb078AlphaDummy658 g) from (by
                        unfold nb078AlphaDummy658;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0674 g) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy649) ≠ (nb078AlphaDummy655) from (by
                          unfold nb078AlphaDummy655;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0672) 0))))
                      (show (nb078AlphaDummy651 g) ≠ (nb078AlphaDummy657 g) from (by
                          unfold nb078AlphaDummy657;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0674 g) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy649) ≠ (nb078AlphaDummy661) from (by
                            unfold nb078AlphaDummy661;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0676) 0))))
                        (show (nb078AlphaDummy651 g) ≠ (nb078AlphaDummy662 g) from (by
                            unfold nb078AlphaDummy662;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0677 g) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy649) ≠ (nb078AlphaDummy659) from (by
                              unfold nb078AlphaDummy659;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0673) 0))))
                          (show (nb078AlphaDummy651 g) ≠ (nb078AlphaDummy660 g) from (by
                              unfold nb078AlphaDummy660;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0675 g) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((synCcnv (Class.cv (nb078AlphaDummy001)))).fv) (by decide))
                            (freshVar_injective (((synCcnv (Class.cv g))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078AlphaDummy649))).fv ∪
                        ((Class.cv (nb078AlphaDummy650))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy651 g))).fv ∪
                        ((Class.cv (nb078AlphaDummy652 g))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy656) ≠ (nb078AlphaDummy663) from (by
                                unfold nb078AlphaDummy663;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0678) 0))))
                            (show (nb078AlphaDummy658 g) ≠ (nb078AlphaDummy665 g) from (by
                                unfold nb078AlphaDummy665;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0679 g) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy656) ≠ (nb078AlphaDummy664) from (by
                                  unfold nb078AlphaDummy664;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0678) 1))))
                              (show (nb078AlphaDummy658 g) ≠ (nb078AlphaDummy666 g) from
                                (by
                                  unfold nb078AlphaDummy666;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0679 g) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy656))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy658 g))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy663) ≠ (nb078AlphaDummy670) from (by
          unfold nb078AlphaDummy670;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0682) 1)))) (show (nb078AlphaDummy665 g) ≠
        (nb078AlphaDummy673 g) from (by
          unfold nb078AlphaDummy673;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0683 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy663) ≠ (nb078AlphaDummy669) from (by
          unfold nb078AlphaDummy669;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0682) 0)))) (show (nb078AlphaDummy665 g) ≠
        (nb078AlphaDummy672 g) from (by
          unfold nb078AlphaDummy672;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0683 g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy663) ≠ (nb078AlphaDummy667)
        from (by
          unfold nb078AlphaDummy667;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0680)
                  0)))) (show (nb078AlphaDummy665 g) ≠ (nb078AlphaDummy668 g) from (by
          unfold nb078AlphaDummy668;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0681 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy671), (nb078AlphaDummy674 g)), ((nb078AlphaDummy670),
        (nb078AlphaDummy673 g)), ((nb078AlphaDummy669), (nb078AlphaDummy672 g)),
        ((nb078AlphaDummy667), (nb078AlphaDummy668 g)), ((nb078AlphaDummy663),
        (nb078AlphaDummy665 g)), ((nb078AlphaDummy664), (nb078AlphaDummy666 g)),
        ((nb078AlphaDummy656), (nb078AlphaDummy658 g)), ((nb078AlphaDummy655),
        (nb078AlphaDummy657 g)), ((nb078AlphaDummy661), (nb078AlphaDummy662 g)),
        ((nb078AlphaDummy659), (nb078AlphaDummy660 g)), ((nb078AlphaDummy650),
        (nb078AlphaDummy652 g)), ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
        ((nb078AlphaDummy653), (nb078AlphaDummy654 g)), ((nb078AlphaDummy571),
        (nb078AlphaDummy574 g)), ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)), ((nb078AlphaDummy575),
        (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy670) ≠ (nb078AlphaDummy677) from (by
          unfold
            nb078AlphaDummy677;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0686)
                  0)))) (show (nb078AlphaDummy673 g) ≠ (nb078AlphaDummy678 g) from (by
          unfold
            nb078AlphaDummy678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0687
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy670) ≠ (nb078AlphaDummy675)
        from (by
          unfold
            nb078AlphaDummy675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0684)
                  0)))) (show (nb078AlphaDummy673 g) ≠ (nb078AlphaDummy676 g) from (by
          unfold
            nb078AlphaDummy676;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0685
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy663))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy665 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy671) ≠ (nb078AlphaDummy677)
        from (by
          unfold
            nb078AlphaDummy677;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0690)
                  0)))) (show (nb078AlphaDummy674 g) ≠ (nb078AlphaDummy678 g) from (by
          unfold
            nb078AlphaDummy678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0691
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy671) ≠ (nb078AlphaDummy675)
        from (by
          unfold
            nb078AlphaDummy675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0688)
                  0)))) (show (nb078AlphaDummy674 g) ≠ (nb078AlphaDummy676 g) from (by
          unfold
            nb078AlphaDummy676;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0689
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy670) ≠ (nb078AlphaDummy677) from (by
          unfold
            nb078AlphaDummy677;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0686)
                  0)))) (show (nb078AlphaDummy673 g) ≠ (nb078AlphaDummy678 g) from (by
          unfold
            nb078AlphaDummy678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0687
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy670) ≠ (nb078AlphaDummy675)
        from (by
          unfold
            nb078AlphaDummy675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0684)
                  0)))) (show (nb078AlphaDummy673 g) ≠ (nb078AlphaDummy676 g) from (by
          unfold
            nb078AlphaDummy676;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0685
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy663))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy665 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy671) ≠ (nb078AlphaDummy677)
        from (by
          unfold
            nb078AlphaDummy677;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0690)
                  0)))) (show (nb078AlphaDummy674 g) ≠ (nb078AlphaDummy678 g) from (by
          unfold
            nb078AlphaDummy678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0691
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy671) ≠ (nb078AlphaDummy675)
        from (by
          unfold
            nb078AlphaDummy675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0688)
                  0)))) (show (nb078AlphaDummy674 g) ≠ (nb078AlphaDummy676 g) from (by
          unfold
            nb078AlphaDummy676;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0689
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy671), (nb078AlphaDummy674 g)), ((nb078AlphaDummy670),
        (nb078AlphaDummy673 g)), ((nb078AlphaDummy669), (nb078AlphaDummy672 g)),
        ((nb078AlphaDummy667), (nb078AlphaDummy668 g)), ((nb078AlphaDummy663),
        (nb078AlphaDummy665 g)), ((nb078AlphaDummy664), (nb078AlphaDummy666 g)),
        ((nb078AlphaDummy656), (nb078AlphaDummy658 g)), ((nb078AlphaDummy655),
        (nb078AlphaDummy657 g)), ((nb078AlphaDummy661), (nb078AlphaDummy662 g)),
        ((nb078AlphaDummy659), (nb078AlphaDummy660 g)), ((nb078AlphaDummy650),
        (nb078AlphaDummy652 g)), ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
        ((nb078AlphaDummy653), (nb078AlphaDummy654 g)), ((nb078AlphaDummy571),
        (nb078AlphaDummy574 g)), ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)), ((nb078AlphaDummy575),
        (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy663))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy665 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy663))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy665
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy670) ≠ (nb078AlphaDummy681) from (by
          unfold
            nb078AlphaDummy681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0694)
                  0)))) (show (nb078AlphaDummy673 g) ≠ (nb078AlphaDummy682 g) from (by
          unfold
            nb078AlphaDummy682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0695
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy670) ≠ (nb078AlphaDummy679)
        from (by
          unfold
            nb078AlphaDummy679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0692)
                  0)))) (show (nb078AlphaDummy673 g) ≠ (nb078AlphaDummy680 g) from (by
          unfold
            nb078AlphaDummy680;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0693
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy663))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy665 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy670) ≠ (nb078AlphaDummy681)
        from (by
          unfold
            nb078AlphaDummy681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0694)
                  0)))) (show (nb078AlphaDummy673 g) ≠ (nb078AlphaDummy682 g) from (by
          unfold
            nb078AlphaDummy682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0695
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy670) ≠ (nb078AlphaDummy679)
        from (by
          unfold
            nb078AlphaDummy679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0692)
                  0)))) (show (nb078AlphaDummy673 g) ≠ (nb078AlphaDummy680 g) from (by
          unfold
            nb078AlphaDummy680;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0693
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy663))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy665 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy671) ≠ (nb078AlphaDummy683) from (by
          unfold
            nb078AlphaDummy683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0698)
                  0)))) (show (nb078AlphaDummy674 g) ≠ (nb078AlphaDummy684 g) from (by
          unfold
            nb078AlphaDummy684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0699
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy671) ≠ (nb078AlphaDummy679)
        from (by
          unfold
            nb078AlphaDummy679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0696)
                  0)))) (show (nb078AlphaDummy674 g) ≠ (nb078AlphaDummy680 g) from (by
          unfold
            nb078AlphaDummy680;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0697
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy671) ≠
        (nb078AlphaDummy683) from (by
          unfold
            nb078AlphaDummy683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0698)
                  0)))) (show (nb078AlphaDummy674 g) ≠ (nb078AlphaDummy684 g) from (by
          unfold
            nb078AlphaDummy684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0699
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy671) ≠ (nb078AlphaDummy679)
        from (by
          unfold
            nb078AlphaDummy679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0696)
                  0)))) (show (nb078AlphaDummy674 g) ≠ (nb078AlphaDummy680 g) from (by
          unfold
            nb078AlphaDummy680;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0697
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy663) ≠ (nb078AlphaDummy667) from
                                        (by
                                          unfold nb078AlphaDummy667;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0680)
                                                  0)))) (show (nb078AlphaDummy665 g) ≠
        (nb078AlphaDummy668 g) from (by
                                          unfold nb078AlphaDummy668;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0681 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy667), (nb078AlphaDummy668 g)),
                                      ((nb078AlphaDummy663), (nb078AlphaDummy665 g)),
                                      ((nb078AlphaDummy664), (nb078AlphaDummy666 g)),
                                      ((nb078AlphaDummy656), (nb078AlphaDummy658 g)),
                                      ((nb078AlphaDummy655), (nb078AlphaDummy657 g)),
                                      ((nb078AlphaDummy661), (nb078AlphaDummy662 g)),
                                      ((nb078AlphaDummy659), (nb078AlphaDummy660 g)),
                                      ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
                                      ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
                                      ((nb078AlphaDummy653), (nb078AlphaDummy654 g)),
                                      ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                                      ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                                      ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                                      ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                                      ((nb078AlphaDummy001), g),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy663) ≠ (nb078AlphaDummy667) from (by
                                        unfold nb078AlphaDummy667;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0680)
                                                0)))) (show (nb078AlphaDummy665 g) ≠
                                        (nb078AlphaDummy668 g) from (by
                                        unfold nb078AlphaDummy668;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0681 g)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy663) ≠ (nb078AlphaDummy667) from
                                        (by
                                          unfold nb078AlphaDummy667;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0680)
                                                  0)))) (show (nb078AlphaDummy665 g) ≠
        (nb078AlphaDummy668 g) from (by
                                          unfold nb078AlphaDummy668;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0681 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy667), (nb078AlphaDummy668 g)),
                                      ((nb078AlphaDummy663), (nb078AlphaDummy665 g)),
                                      ((nb078AlphaDummy664), (nb078AlphaDummy666 g)),
                                      ((nb078AlphaDummy656), (nb078AlphaDummy658 g)),
                                      ((nb078AlphaDummy655), (nb078AlphaDummy657 g)),
                                      ((nb078AlphaDummy661), (nb078AlphaDummy662 g)),
                                      ((nb078AlphaDummy659), (nb078AlphaDummy660 g)),
                                      ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
                                      ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
                                      ((nb078AlphaDummy653), (nb078AlphaDummy654 g)),
                                      ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                                      ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                                      ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                                      ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                                      ((nb078AlphaDummy001), g),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part112`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0087`. -/
@[expose]
noncomputable def nb078SplitAlpha0087 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078AlphaDummy689), (nb078AlphaDummy690 g)),
        ((nb078AlphaDummy687), (nb078AlphaDummy688 g)),
        ((nb078AlphaDummy656), (nb078AlphaDummy658 g)),
        ((nb078AlphaDummy655), (nb078AlphaDummy657 g)),
        ((nb078AlphaDummy685), (nb078AlphaDummy686 g)),
        ((nb078AlphaDummy659), (nb078AlphaDummy660 g)),
        ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
        ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
        ((nb078AlphaDummy653), (nb078AlphaDummy654 g)),
        ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
        ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy689))
          (synCphi (Class.cv (nb078AlphaDummy656)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy689))
            (synCphi (Class.cv (nb078AlphaDummy656))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy690 g))
          (synCphi (Class.cv (nb078AlphaDummy658 g)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy690 g))
            (synCphi (Class.cv (nb078AlphaDummy658 g)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy656) ≠ (nb078AlphaDummy663) from
                    (by
                      unfold nb078AlphaDummy663;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0678) 0))))
                  (show (nb078AlphaDummy658 g) ≠ (nb078AlphaDummy665 g) from (by
                      unfold nb078AlphaDummy665;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0679 g) 0))))
                  (TAlphaVar.there (show (nb078AlphaDummy656) ≠ (nb078AlphaDummy664) from
                      (by
                        unfold nb078AlphaDummy664;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0678) 1))))
                    (show (nb078AlphaDummy658 g) ≠ (nb078AlphaDummy666 g) from (by
                        unfold nb078AlphaDummy666;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0679 g) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy656) ≠ (nb078AlphaDummy689) from (by
                          unfold nb078AlphaDummy689;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0708) 0))))
                      (show (nb078AlphaDummy658 g) ≠ (nb078AlphaDummy690 g) from (by
                          unfold nb078AlphaDummy690;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0709 g) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy656) ≠ (nb078AlphaDummy687) from (by
                            unfold nb078AlphaDummy687;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0706) 0))))
                        (show (nb078AlphaDummy658 g) ≠ (nb078AlphaDummy688 g) from (by
                            unfold nb078AlphaDummy688;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0707 g) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy656))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy658 g))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy663) ≠ (nb078AlphaDummy670) from (by
                                        unfold nb078AlphaDummy670;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0682)
                                                1)))) (show (nb078AlphaDummy665 g) ≠
                                        (nb078AlphaDummy673 g) from (by
                                        unfold nb078AlphaDummy673;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0683 g)
                                                1)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy663) ≠ (nb078AlphaDummy669) from
                                        (by
                                          unfold nb078AlphaDummy669;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0682)
                                                  0)))) (show (nb078AlphaDummy665 g) ≠
        (nb078AlphaDummy672 g) from (by
                                          unfold nb078AlphaDummy672;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0683 g) 0))))
                                      (TAlphaVar.there (show (nb078AlphaDummy663) ≠
        (nb078AlphaDummy667) from (by
          unfold nb078AlphaDummy667;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0680) 0)))) (show (nb078AlphaDummy665 g) ≠
        (nb078AlphaDummy668 g) from (by
          unfold nb078AlphaDummy668;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0681 g) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb078AlphaDummy671),
        (nb078AlphaDummy674 g)), ((nb078AlphaDummy670), (nb078AlphaDummy673 g)),
                                        ((nb078AlphaDummy669), (nb078AlphaDummy672 g)),
                                        ((nb078AlphaDummy667), (nb078AlphaDummy668 g)),
                                        ((nb078AlphaDummy663), (nb078AlphaDummy665 g)),
                                        ((nb078AlphaDummy664), (nb078AlphaDummy666 g)),
                                        ((nb078AlphaDummy689), (nb078AlphaDummy690 g)),
                                        ((nb078AlphaDummy687), (nb078AlphaDummy688 g)),
                                        ((nb078AlphaDummy656), (nb078AlphaDummy658 g)),
                                        ((nb078AlphaDummy655), (nb078AlphaDummy657 g)),
                                        ((nb078AlphaDummy685), (nb078AlphaDummy686 g)),
                                        ((nb078AlphaDummy659), (nb078AlphaDummy660 g)),
                                        ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
                                        ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
                                        ((nb078AlphaDummy653), (nb078AlphaDummy654 g)),
                                        ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                                        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                                        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                                        ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                                        ((nb078AlphaDummy001), g),
                                        ((nb078AlphaDummy004), y),
                                        ((nb078AlphaDummy003), x)]
                                      (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy670) ≠
        (nb078AlphaDummy677) from (by
          unfold
            nb078AlphaDummy677;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0686)
                  0)))) (show (nb078AlphaDummy673 g) ≠ (nb078AlphaDummy678 g) from (by
          unfold
            nb078AlphaDummy678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0687
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy670) ≠ (nb078AlphaDummy675)
        from (by
          unfold
            nb078AlphaDummy675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0684)
                  0)))) (show (nb078AlphaDummy673 g) ≠ (nb078AlphaDummy676 g) from (by
          unfold
            nb078AlphaDummy676;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0685
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy663))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy665 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy671) ≠ (nb078AlphaDummy677)
        from (by
          unfold
            nb078AlphaDummy677;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0690)
                  0)))) (show (nb078AlphaDummy674 g) ≠ (nb078AlphaDummy678 g) from (by
          unfold
            nb078AlphaDummy678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0691
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy671) ≠ (nb078AlphaDummy675)
        from (by
          unfold
            nb078AlphaDummy675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0688)
                  0)))) (show (nb078AlphaDummy674 g) ≠ (nb078AlphaDummy676 g) from (by
          unfold
            nb078AlphaDummy676;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0689
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy670) ≠ (nb078AlphaDummy677) from (by
          unfold
            nb078AlphaDummy677;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0686)
                  0)))) (show (nb078AlphaDummy673 g) ≠ (nb078AlphaDummy678 g) from (by
          unfold
            nb078AlphaDummy678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0687
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy670) ≠ (nb078AlphaDummy675)
        from (by
          unfold
            nb078AlphaDummy675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0684)
                  0)))) (show (nb078AlphaDummy673 g) ≠ (nb078AlphaDummy676 g) from (by
          unfold
            nb078AlphaDummy676;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0685
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy663))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy665 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy671) ≠ (nb078AlphaDummy677)
        from (by
          unfold
            nb078AlphaDummy677;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0690)
                  0)))) (show (nb078AlphaDummy674 g) ≠ (nb078AlphaDummy678 g) from (by
          unfold
            nb078AlphaDummy678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0691
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy671) ≠ (nb078AlphaDummy675)
        from (by
          unfold
            nb078AlphaDummy675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0688)
                  0)))) (show (nb078AlphaDummy674 g) ≠ (nb078AlphaDummy676 g) from (by
          unfold
            nb078AlphaDummy676;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0689
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb078AlphaDummy671), (nb078AlphaDummy674 g)),
        ((nb078AlphaDummy670), (nb078AlphaDummy673 g)), ((nb078AlphaDummy669),
        (nb078AlphaDummy672 g)), ((nb078AlphaDummy667), (nb078AlphaDummy668 g)),
        ((nb078AlphaDummy663), (nb078AlphaDummy665 g)), ((nb078AlphaDummy664),
        (nb078AlphaDummy666 g)), ((nb078AlphaDummy689), (nb078AlphaDummy690 g)),
        ((nb078AlphaDummy687), (nb078AlphaDummy688 g)), ((nb078AlphaDummy656),
        (nb078AlphaDummy658 g)), ((nb078AlphaDummy655), (nb078AlphaDummy657 g)),
        ((nb078AlphaDummy685), (nb078AlphaDummy686 g)), ((nb078AlphaDummy659),
        (nb078AlphaDummy660 g)), ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
        ((nb078AlphaDummy649), (nb078AlphaDummy651 g)), ((nb078AlphaDummy653),
        (nb078AlphaDummy654 g)), ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)), ((nb078AlphaDummy569),
        (nb078AlphaDummy572 g)), ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy663))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078AlphaDummy665 g))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy663))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078AlphaDummy665 g))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy670) ≠
        (nb078AlphaDummy681) from (by
          unfold
            nb078AlphaDummy681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0694)
                  0)))) (show (nb078AlphaDummy673 g) ≠ (nb078AlphaDummy682 g) from (by
          unfold
            nb078AlphaDummy682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0695
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy670) ≠ (nb078AlphaDummy679)
        from (by
          unfold
            nb078AlphaDummy679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0692)
                  0)))) (show (nb078AlphaDummy673 g) ≠ (nb078AlphaDummy680 g) from (by
          unfold
            nb078AlphaDummy680;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0693
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy663))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy665 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy670) ≠ (nb078AlphaDummy681)
        from (by
          unfold
            nb078AlphaDummy681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0694)
                  0)))) (show (nb078AlphaDummy673 g) ≠ (nb078AlphaDummy682 g) from (by
          unfold
            nb078AlphaDummy682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0695
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy670) ≠ (nb078AlphaDummy679)
        from (by
          unfold
            nb078AlphaDummy679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0692)
                  0)))) (show (nb078AlphaDummy673 g) ≠ (nb078AlphaDummy680 g) from (by
          unfold
            nb078AlphaDummy680;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0693
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy663))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy665 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy671) ≠ (nb078AlphaDummy683) from (by
          unfold
            nb078AlphaDummy683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0698)
                  0)))) (show (nb078AlphaDummy674 g) ≠ (nb078AlphaDummy684 g) from (by
          unfold
            nb078AlphaDummy684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0699
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy671) ≠ (nb078AlphaDummy679)
        from (by
          unfold
            nb078AlphaDummy679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0696)
                  0)))) (show (nb078AlphaDummy674 g) ≠ (nb078AlphaDummy680 g) from (by
          unfold
            nb078AlphaDummy680;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0697
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy671) ≠
        (nb078AlphaDummy683) from (by
          unfold
            nb078AlphaDummy683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0698)
                  0)))) (show (nb078AlphaDummy674 g) ≠ (nb078AlphaDummy684 g) from (by
          unfold
            nb078AlphaDummy684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0699
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy671) ≠ (nb078AlphaDummy679)
        from (by
          unfold
            nb078AlphaDummy679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0696)
                  0)))) (show (nb078AlphaDummy674 g) ≠ (nb078AlphaDummy680 g) from (by
          unfold
            nb078AlphaDummy680;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0697
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy663) ≠ (nb078AlphaDummy667) from (by
                                unfold nb078AlphaDummy667;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0680) 0))))
                            (show (nb078AlphaDummy665 g) ≠ (nb078AlphaDummy668 g) from (by
                                unfold nb078AlphaDummy668;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0681 g) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb078AlphaDummy667), (nb078AlphaDummy668 g)),
                            ((nb078AlphaDummy663), (nb078AlphaDummy665 g)),
                            ((nb078AlphaDummy664), (nb078AlphaDummy666 g)),
                            ((nb078AlphaDummy689), (nb078AlphaDummy690 g)),
                            ((nb078AlphaDummy687), (nb078AlphaDummy688 g)),
                            ((nb078AlphaDummy656), (nb078AlphaDummy658 g)),
                            ((nb078AlphaDummy655), (nb078AlphaDummy657 g)),
                            ((nb078AlphaDummy685), (nb078AlphaDummy686 g)),
                            ((nb078AlphaDummy659), (nb078AlphaDummy660 g)),
                            ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
                            ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
                            ((nb078AlphaDummy653), (nb078AlphaDummy654 g)),
                            ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                            ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                            ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                            ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                            ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                            ((nb078AlphaDummy003), x)]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy663) ≠ (nb078AlphaDummy667) from (by
                              unfold nb078AlphaDummy667;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0680) 0))))
                          (show (nb078AlphaDummy665 g) ≠ (nb078AlphaDummy668 g) from (by
                              unfold nb078AlphaDummy668;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0681 g) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy663) ≠ (nb078AlphaDummy667) from (by
                                unfold nb078AlphaDummy667;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0680) 0))))
                            (show (nb078AlphaDummy665 g) ≠ (nb078AlphaDummy668 g) from (by
                                unfold nb078AlphaDummy668;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0681 g) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb078AlphaDummy667), (nb078AlphaDummy668 g)),
                            ((nb078AlphaDummy663), (nb078AlphaDummy665 g)),
                            ((nb078AlphaDummy664), (nb078AlphaDummy666 g)),
                            ((nb078AlphaDummy689), (nb078AlphaDummy690 g)),
                            ((nb078AlphaDummy687), (nb078AlphaDummy688 g)),
                            ((nb078AlphaDummy656), (nb078AlphaDummy658 g)),
                            ((nb078AlphaDummy655), (nb078AlphaDummy657 g)),
                            ((nb078AlphaDummy685), (nb078AlphaDummy686 g)),
                            ((nb078AlphaDummy659), (nb078AlphaDummy660 g)),
                            ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
                            ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
                            ((nb078AlphaDummy653), (nb078AlphaDummy654 g)),
                            ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                            ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                            ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                            ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                            ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                            ((nb078AlphaDummy003), x)]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb078AlphaDummy656) ≠ (nb078AlphaDummy663) from (by
                        unfold nb078AlphaDummy663;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0678) 0))))
                    (show (nb078AlphaDummy658 g) ≠ (nb078AlphaDummy665 g) from (by
                        unfold nb078AlphaDummy665;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0679 g) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy656) ≠ (nb078AlphaDummy664) from (by
                          unfold nb078AlphaDummy664;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0678) 1))))
                      (show (nb078AlphaDummy658 g) ≠ (nb078AlphaDummy666 g) from (by
                          unfold nb078AlphaDummy666;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0679 g) 1))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy656) ≠ (nb078AlphaDummy689) from (by
                            unfold nb078AlphaDummy689;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0708) 0))))
                        (show (nb078AlphaDummy658 g) ≠ (nb078AlphaDummy690 g) from (by
                            unfold nb078AlphaDummy690;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0709 g) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy656) ≠ (nb078AlphaDummy687) from (by
                              unfold nb078AlphaDummy687;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0706) 0))))
                          (show (nb078AlphaDummy658 g) ≠ (nb078AlphaDummy688 g) from (by
                              unfold nb078AlphaDummy688;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0707 g) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy656))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy658 g))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb078AlphaDummy663) ≠ (nb078AlphaDummy670) from
                                        (by
                                          unfold nb078AlphaDummy670;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0682)
                                                  1)))) (show (nb078AlphaDummy665 g) ≠
        (nb078AlphaDummy673 g) from (by
                                          unfold nb078AlphaDummy673;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0683 g) 1))))
                                      (TAlphaVar.there (show (nb078AlphaDummy663) ≠
        (nb078AlphaDummy669) from (by
          unfold nb078AlphaDummy669;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0682) 0)))) (show (nb078AlphaDummy665 g) ≠
        (nb078AlphaDummy672 g) from (by
          unfold nb078AlphaDummy672;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0683 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy663) ≠ (nb078AlphaDummy667) from (by
          unfold nb078AlphaDummy667;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0680) 0)))) (show (nb078AlphaDummy665 g) ≠
        (nb078AlphaDummy668 g) from (by
          unfold nb078AlphaDummy668;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0681 g) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb078AlphaDummy671),
        (nb078AlphaDummy674 g)), ((nb078AlphaDummy670), (nb078AlphaDummy673 g)),
        ((nb078AlphaDummy669), (nb078AlphaDummy672 g)), ((nb078AlphaDummy667),
        (nb078AlphaDummy668 g)), ((nb078AlphaDummy663), (nb078AlphaDummy665 g)),
        ((nb078AlphaDummy664), (nb078AlphaDummy666 g)), ((nb078AlphaDummy689),
        (nb078AlphaDummy690 g)), ((nb078AlphaDummy687), (nb078AlphaDummy688 g)),
        ((nb078AlphaDummy656), (nb078AlphaDummy658 g)), ((nb078AlphaDummy655),
        (nb078AlphaDummy657 g)), ((nb078AlphaDummy685), (nb078AlphaDummy686 g)),
        ((nb078AlphaDummy659), (nb078AlphaDummy660 g)), ((nb078AlphaDummy650),
        (nb078AlphaDummy652 g)), ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
        ((nb078AlphaDummy653), (nb078AlphaDummy654 g)), ((nb078AlphaDummy571),
        (nb078AlphaDummy574 g)), ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)), ((nb078AlphaDummy575),
        (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy670) ≠
        (nb078AlphaDummy677) from (by
          unfold
            nb078AlphaDummy677;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0686)
                  0)))) (show (nb078AlphaDummy673 g) ≠ (nb078AlphaDummy678 g) from (by
          unfold
            nb078AlphaDummy678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0687
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy670) ≠ (nb078AlphaDummy675)
        from (by
          unfold
            nb078AlphaDummy675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0684)
                  0)))) (show (nb078AlphaDummy673 g) ≠ (nb078AlphaDummy676 g) from (by
          unfold
            nb078AlphaDummy676;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0685
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy663))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy665 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy671) ≠ (nb078AlphaDummy677)
        from (by
          unfold
            nb078AlphaDummy677;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0690)
                  0)))) (show (nb078AlphaDummy674 g) ≠ (nb078AlphaDummy678 g) from (by
          unfold
            nb078AlphaDummy678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0691
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy671) ≠ (nb078AlphaDummy675)
        from (by
          unfold
            nb078AlphaDummy675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0688)
                  0)))) (show (nb078AlphaDummy674 g) ≠ (nb078AlphaDummy676 g) from (by
          unfold
            nb078AlphaDummy676;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0689
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy670) ≠ (nb078AlphaDummy677) from (by
          unfold
            nb078AlphaDummy677;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0686)
                  0)))) (show (nb078AlphaDummy673 g) ≠ (nb078AlphaDummy678 g) from (by
          unfold
            nb078AlphaDummy678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0687
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy670) ≠ (nb078AlphaDummy675)
        from (by
          unfold
            nb078AlphaDummy675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0684)
                  0)))) (show (nb078AlphaDummy673 g) ≠ (nb078AlphaDummy676 g) from (by
          unfold
            nb078AlphaDummy676;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0685
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy663))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy665 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy671) ≠ (nb078AlphaDummy677)
        from (by
          unfold
            nb078AlphaDummy677;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0690)
                  0)))) (show (nb078AlphaDummy674 g) ≠ (nb078AlphaDummy678 g) from (by
          unfold
            nb078AlphaDummy678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0691
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy671) ≠ (nb078AlphaDummy675)
        from (by
          unfold
            nb078AlphaDummy675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0688)
                  0)))) (show (nb078AlphaDummy674 g) ≠ (nb078AlphaDummy676 g) from (by
          unfold
            nb078AlphaDummy676;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0689
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy671), (nb078AlphaDummy674 g)), ((nb078AlphaDummy670),
        (nb078AlphaDummy673 g)), ((nb078AlphaDummy669), (nb078AlphaDummy672 g)),
        ((nb078AlphaDummy667), (nb078AlphaDummy668 g)), ((nb078AlphaDummy663),
        (nb078AlphaDummy665 g)), ((nb078AlphaDummy664), (nb078AlphaDummy666 g)),
        ((nb078AlphaDummy689), (nb078AlphaDummy690 g)), ((nb078AlphaDummy687),
        (nb078AlphaDummy688 g)), ((nb078AlphaDummy656), (nb078AlphaDummy658 g)),
        ((nb078AlphaDummy655), (nb078AlphaDummy657 g)), ((nb078AlphaDummy685),
        (nb078AlphaDummy686 g)), ((nb078AlphaDummy659), (nb078AlphaDummy660 g)),
        ((nb078AlphaDummy650), (nb078AlphaDummy652 g)), ((nb078AlphaDummy649),
        (nb078AlphaDummy651 g)), ((nb078AlphaDummy653), (nb078AlphaDummy654 g)),
        ((nb078AlphaDummy571), (nb078AlphaDummy574 g)), ((nb078AlphaDummy570),
        (nb078AlphaDummy573 g)), ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
        ((nb078AlphaDummy575), (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy663))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy665 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy663))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy665 g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy670) ≠
        (nb078AlphaDummy681) from (by
          unfold
            nb078AlphaDummy681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0694)
                  0)))) (show (nb078AlphaDummy673 g) ≠ (nb078AlphaDummy682 g) from (by
          unfold
            nb078AlphaDummy682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0695
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy670) ≠ (nb078AlphaDummy679)
        from (by
          unfold
            nb078AlphaDummy679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0692)
                  0)))) (show (nb078AlphaDummy673 g) ≠ (nb078AlphaDummy680 g) from (by
          unfold
            nb078AlphaDummy680;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0693
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy663))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy665 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy670) ≠ (nb078AlphaDummy681)
        from (by
          unfold
            nb078AlphaDummy681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0694)
                  0)))) (show (nb078AlphaDummy673 g) ≠ (nb078AlphaDummy682 g) from (by
          unfold
            nb078AlphaDummy682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0695
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy670) ≠ (nb078AlphaDummy679)
        from (by
          unfold
            nb078AlphaDummy679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0692)
                  0)))) (show (nb078AlphaDummy673 g) ≠ (nb078AlphaDummy680 g) from (by
          unfold
            nb078AlphaDummy680;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0693
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy663))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy665 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy671) ≠ (nb078AlphaDummy683) from (by
          unfold
            nb078AlphaDummy683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0698)
                  0)))) (show (nb078AlphaDummy674 g) ≠ (nb078AlphaDummy684 g) from (by
          unfold
            nb078AlphaDummy684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0699
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy671) ≠ (nb078AlphaDummy679)
        from (by
          unfold
            nb078AlphaDummy679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0696)
                  0)))) (show (nb078AlphaDummy674 g) ≠ (nb078AlphaDummy680 g) from (by
          unfold
            nb078AlphaDummy680;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0697
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy671) ≠
        (nb078AlphaDummy683) from (by
          unfold
            nb078AlphaDummy683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0698)
                  0)))) (show (nb078AlphaDummy674 g) ≠ (nb078AlphaDummy684 g) from (by
          unfold
            nb078AlphaDummy684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0699
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy671) ≠ (nb078AlphaDummy679)
        from (by
          unfold
            nb078AlphaDummy679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0696)
                  0)))) (show (nb078AlphaDummy674 g) ≠ (nb078AlphaDummy680 g) from (by
          unfold
            nb078AlphaDummy680;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0697
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078AlphaDummy663) ≠ (nb078AlphaDummy667) from (by
                                  unfold nb078AlphaDummy667;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0680) 0))))
                              (show (nb078AlphaDummy665 g) ≠ (nb078AlphaDummy668 g) from
                                (by
                                  unfold nb078AlphaDummy668;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0681 g) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb078AlphaDummy667), (nb078AlphaDummy668 g)),
                              ((nb078AlphaDummy663), (nb078AlphaDummy665 g)),
                              ((nb078AlphaDummy664), (nb078AlphaDummy666 g)),
                              ((nb078AlphaDummy689), (nb078AlphaDummy690 g)),
                              ((nb078AlphaDummy687), (nb078AlphaDummy688 g)),
                              ((nb078AlphaDummy656), (nb078AlphaDummy658 g)),
                              ((nb078AlphaDummy655), (nb078AlphaDummy657 g)),
                              ((nb078AlphaDummy685), (nb078AlphaDummy686 g)),
                              ((nb078AlphaDummy659), (nb078AlphaDummy660 g)),
                              ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
                              ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
                              ((nb078AlphaDummy653), (nb078AlphaDummy654 g)),
                              ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                              ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                              ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                              ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                              ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                              ((nb078AlphaDummy003), x)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy663) ≠ (nb078AlphaDummy667) from (by
                                unfold nb078AlphaDummy667;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0680) 0))))
                            (show (nb078AlphaDummy665 g) ≠ (nb078AlphaDummy668 g) from (by
                                unfold nb078AlphaDummy668;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0681 g) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078AlphaDummy663) ≠ (nb078AlphaDummy667) from (by
                                  unfold nb078AlphaDummy667;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0680) 0))))
                              (show (nb078AlphaDummy665 g) ≠ (nb078AlphaDummy668 g) from
                                (by
                                  unfold nb078AlphaDummy668;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0681 g) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb078AlphaDummy667), (nb078AlphaDummy668 g)),
                              ((nb078AlphaDummy663), (nb078AlphaDummy665 g)),
                              ((nb078AlphaDummy664), (nb078AlphaDummy666 g)),
                              ((nb078AlphaDummy689), (nb078AlphaDummy690 g)),
                              ((nb078AlphaDummy687), (nb078AlphaDummy688 g)),
                              ((nb078AlphaDummy656), (nb078AlphaDummy658 g)),
                              ((nb078AlphaDummy655), (nb078AlphaDummy657 g)),
                              ((nb078AlphaDummy685), (nb078AlphaDummy686 g)),
                              ((nb078AlphaDummy659), (nb078AlphaDummy660 g)),
                              ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
                              ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
                              ((nb078AlphaDummy653), (nb078AlphaDummy654 g)),
                              ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                              ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                              ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                              ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                              ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                              ((nb078AlphaDummy003), x)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
