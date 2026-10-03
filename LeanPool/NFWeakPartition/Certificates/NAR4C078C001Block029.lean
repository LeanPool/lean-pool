/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block028

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part092`. -/


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
noncomputable def nb078_split_alpha_0065 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_645), (nb078_alpha_dummy_646 g)),
        ((nb078_alpha_dummy_614), (nb078_alpha_dummy_616 g)),
        ((nb078_alpha_dummy_613), (nb078_alpha_dummy_615 g)),
        ((nb078_alpha_dummy_643), (nb078_alpha_dummy_644 g)),
        ((nb078_alpha_dummy_617), (nb078_alpha_dummy_618 g)),
        ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
        ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
        ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.classMem (Class.cv (nb078_alpha_dummy_645))
        (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_614)))))
      (Wff.classMem (Class.cv (nb078_alpha_dummy_646 g))
        (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_616 g))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_614) ≠ (nb078_alpha_dummy_621) from (by
                            unfold nb078_alpha_dummy_621;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0636) 0))))
                        (show (nb078_alpha_dummy_616 g) ≠ (nb078_alpha_dummy_623 g) from (by
                            unfold nb078_alpha_dummy_623;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0637 g) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_614) ≠ (nb078_alpha_dummy_622) from (by
                              unfold nb078_alpha_dummy_622;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0636) 1))))
                          (show (nb078_alpha_dummy_616 g) ≠ (nb078_alpha_dummy_624 g) from (by
                              unfold nb078_alpha_dummy_624;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0637 g) 1))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_614) ≠ (nb078_alpha_dummy_647) from (by
                                unfold nb078_alpha_dummy_647;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0666) 0))))
                            (show (nb078_alpha_dummy_616 g) ≠ (nb078_alpha_dummy_648 g) from (by
                                unfold nb078_alpha_dummy_648;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0667 g) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_614) ≠ (nb078_alpha_dummy_645) from (by
                                  unfold nb078_alpha_dummy_645;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0664) 0))))
                              (show (nb078_alpha_dummy_616 g) ≠ (nb078_alpha_dummy_646 g) from
                                (by
                                  unfold nb078_alpha_dummy_646;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0665 g) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there
                        (freshVar_injective (((Class.cv (nb078_alpha_dummy_614))).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv (nb078_alpha_dummy_616 g))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078_alpha_dummy_621) ≠
        (nb078_alpha_dummy_628) from (by
          unfold nb078_alpha_dummy_628;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0640) 1)))) (show (nb078_alpha_dummy_623 g) ≠
        (nb078_alpha_dummy_631 g) from (by
          unfold nb078_alpha_dummy_631;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0641 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_621) ≠ (nb078_alpha_dummy_627) from (by
          unfold nb078_alpha_dummy_627;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0640) 0)))) (show (nb078_alpha_dummy_623 g) ≠
        (nb078_alpha_dummy_630 g) from (by
          unfold nb078_alpha_dummy_630;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0641 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_621) ≠ (nb078_alpha_dummy_625) from (by
          unfold nb078_alpha_dummy_625;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0638) 0)))) (show (nb078_alpha_dummy_623 g) ≠
        (nb078_alpha_dummy_626 g) from (by
          unfold nb078_alpha_dummy_626;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0639 g) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_629), (nb078_alpha_dummy_632 g)), ((nb078_alpha_dummy_628),
        (nb078_alpha_dummy_631 g)), ((nb078_alpha_dummy_627), (nb078_alpha_dummy_630 g)),
        ((nb078_alpha_dummy_625), (nb078_alpha_dummy_626 g)), ((nb078_alpha_dummy_621),
        (nb078_alpha_dummy_623 g)), ((nb078_alpha_dummy_622), (nb078_alpha_dummy_624 g)),
        ((nb078_alpha_dummy_647), (nb078_alpha_dummy_648 g)), ((nb078_alpha_dummy_645),
        (nb078_alpha_dummy_646 g)), ((nb078_alpha_dummy_614), (nb078_alpha_dummy_616 g)),
        ((nb078_alpha_dummy_613), (nb078_alpha_dummy_615 g)), ((nb078_alpha_dummy_643),
        (nb078_alpha_dummy_644 g)), ((nb078_alpha_dummy_617), (nb078_alpha_dummy_618 g)),
        ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570),
        (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
        ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567),
        (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_628) ≠ (nb078_alpha_dummy_635) from (by
          unfold
            nb078_alpha_dummy_635;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0644)
                  0)))) (show (nb078_alpha_dummy_631 g) ≠ (nb078_alpha_dummy_636 g) from (by
          unfold
            nb078_alpha_dummy_636;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0645
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_628) ≠ (nb078_alpha_dummy_633)
        from (by
          unfold
            nb078_alpha_dummy_633;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0642)
                  0)))) (show (nb078_alpha_dummy_631 g) ≠ (nb078_alpha_dummy_634 g) from (by
          unfold
            nb078_alpha_dummy_634;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0643
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_629) ≠ (nb078_alpha_dummy_635)
        from (by
          unfold
            nb078_alpha_dummy_635;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0648)
                  0)))) (show (nb078_alpha_dummy_632 g) ≠ (nb078_alpha_dummy_636 g) from (by
          unfold
            nb078_alpha_dummy_636;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0649
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_629) ≠ (nb078_alpha_dummy_633)
        from (by
          unfold
            nb078_alpha_dummy_633;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0646)
                  0)))) (show (nb078_alpha_dummy_632 g) ≠ (nb078_alpha_dummy_634 g) from (by
          unfold
            nb078_alpha_dummy_634;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0647
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_628) ≠ (nb078_alpha_dummy_635) from (by
          unfold
            nb078_alpha_dummy_635;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0644)
                  0)))) (show (nb078_alpha_dummy_631 g) ≠ (nb078_alpha_dummy_636 g) from (by
          unfold
            nb078_alpha_dummy_636;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0645
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_628) ≠ (nb078_alpha_dummy_633)
        from (by
          unfold
            nb078_alpha_dummy_633;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0642)
                  0)))) (show (nb078_alpha_dummy_631 g) ≠ (nb078_alpha_dummy_634 g) from (by
          unfold
            nb078_alpha_dummy_634;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0643
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_629) ≠ (nb078_alpha_dummy_635)
        from (by
          unfold
            nb078_alpha_dummy_635;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0648)
                  0)))) (show (nb078_alpha_dummy_632 g) ≠ (nb078_alpha_dummy_636 g) from (by
          unfold
            nb078_alpha_dummy_636;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0649
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_629) ≠ (nb078_alpha_dummy_633)
        from (by
          unfold
            nb078_alpha_dummy_633;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0646)
                  0)))) (show (nb078_alpha_dummy_632 g) ≠ (nb078_alpha_dummy_634 g) from (by
          unfold
            nb078_alpha_dummy_634;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0647
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_629), (nb078_alpha_dummy_632 g)), ((nb078_alpha_dummy_628),
        (nb078_alpha_dummy_631 g)), ((nb078_alpha_dummy_627), (nb078_alpha_dummy_630 g)),
        ((nb078_alpha_dummy_625), (nb078_alpha_dummy_626 g)), ((nb078_alpha_dummy_621),
        (nb078_alpha_dummy_623 g)), ((nb078_alpha_dummy_622), (nb078_alpha_dummy_624 g)),
        ((nb078_alpha_dummy_647), (nb078_alpha_dummy_648 g)), ((nb078_alpha_dummy_645),
        (nb078_alpha_dummy_646 g)), ((nb078_alpha_dummy_614), (nb078_alpha_dummy_616 g)),
        ((nb078_alpha_dummy_613), (nb078_alpha_dummy_615 g)), ((nb078_alpha_dummy_643),
        (nb078_alpha_dummy_644 g)), ((nb078_alpha_dummy_617), (nb078_alpha_dummy_618 g)),
        ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570),
        (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
        ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567),
        (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_621))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_628) ≠ (nb078_alpha_dummy_639) from (by
          unfold
            nb078_alpha_dummy_639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0652)
                  0)))) (show (nb078_alpha_dummy_631 g) ≠ (nb078_alpha_dummy_640 g) from (by
          unfold
            nb078_alpha_dummy_640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0653
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_628) ≠ (nb078_alpha_dummy_637)
        from (by
          unfold
            nb078_alpha_dummy_637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0650)
                  0)))) (show (nb078_alpha_dummy_631 g) ≠ (nb078_alpha_dummy_638 g) from (by
          unfold
            nb078_alpha_dummy_638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0651
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_628) ≠ (nb078_alpha_dummy_639)
        from (by
          unfold
            nb078_alpha_dummy_639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0652)
                  0)))) (show (nb078_alpha_dummy_631 g) ≠ (nb078_alpha_dummy_640 g) from (by
          unfold
            nb078_alpha_dummy_640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0653
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_628) ≠ (nb078_alpha_dummy_637)
        from (by
          unfold
            nb078_alpha_dummy_637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0650)
                  0)))) (show (nb078_alpha_dummy_631 g) ≠ (nb078_alpha_dummy_638 g) from (by
          unfold
            nb078_alpha_dummy_638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0651
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_629) ≠ (nb078_alpha_dummy_641) from (by
          unfold
            nb078_alpha_dummy_641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0656)
                  0)))) (show (nb078_alpha_dummy_632 g) ≠ (nb078_alpha_dummy_642 g) from (by
          unfold
            nb078_alpha_dummy_642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0657
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_629) ≠ (nb078_alpha_dummy_637)
        from (by
          unfold
            nb078_alpha_dummy_637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0654)
                  0)))) (show (nb078_alpha_dummy_632 g) ≠ (nb078_alpha_dummy_638 g) from (by
          unfold
            nb078_alpha_dummy_638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0655
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_629) ≠
        (nb078_alpha_dummy_641) from (by
          unfold
            nb078_alpha_dummy_641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0656)
                  0)))) (show (nb078_alpha_dummy_632 g) ≠ (nb078_alpha_dummy_642 g) from (by
          unfold
            nb078_alpha_dummy_642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0657
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_629) ≠ (nb078_alpha_dummy_637)
        from (by
          unfold
            nb078_alpha_dummy_637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0654)
                  0)))) (show (nb078_alpha_dummy_632 g) ≠ (nb078_alpha_dummy_638 g) from (by
          unfold
            nb078_alpha_dummy_638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0655
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_621) ≠ (nb078_alpha_dummy_625) from
                                    (by
                                      unfold nb078_alpha_dummy_625;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0638)
                                              0)))) (show
                                    (nb078_alpha_dummy_623 g) ≠ (nb078_alpha_dummy_626 g) from
                                    (by
                                      unfold nb078_alpha_dummy_626;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0639 g)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed
                                [((nb078_alpha_dummy_625), (nb078_alpha_dummy_626 g)),
                                  ((nb078_alpha_dummy_621), (nb078_alpha_dummy_623 g)),
                                  ((nb078_alpha_dummy_622), (nb078_alpha_dummy_624 g)),
                                  ((nb078_alpha_dummy_647), (nb078_alpha_dummy_648 g)),
                                  ((nb078_alpha_dummy_645), (nb078_alpha_dummy_646 g)),
                                  ((nb078_alpha_dummy_614), (nb078_alpha_dummy_616 g)),
                                  ((nb078_alpha_dummy_613), (nb078_alpha_dummy_615 g)),
                                  ((nb078_alpha_dummy_643), (nb078_alpha_dummy_644 g)),
                                  ((nb078_alpha_dummy_617), (nb078_alpha_dummy_618 g)),
                                  ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                                  ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                                  ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                                  ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                                  ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
                                  ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
                                  ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                                  ((nb078_alpha_dummy_003), x)]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb078_alpha_dummy_621) ≠ (nb078_alpha_dummy_625) from (by
                                    unfold nb078_alpha_dummy_625;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0638) 0)))) (show
                                  (nb078_alpha_dummy_623 g) ≠ (nb078_alpha_dummy_626 g) from (by
                                    unfold nb078_alpha_dummy_626;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0639 g)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_621) ≠ (nb078_alpha_dummy_625) from
                                    (by
                                      unfold nb078_alpha_dummy_625;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0638)
                                              0)))) (show
                                    (nb078_alpha_dummy_623 g) ≠ (nb078_alpha_dummy_626 g) from
                                    (by
                                      unfold nb078_alpha_dummy_626;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0639 g)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed
                                [((nb078_alpha_dummy_625), (nb078_alpha_dummy_626 g)),
                                  ((nb078_alpha_dummy_621), (nb078_alpha_dummy_623 g)),
                                  ((nb078_alpha_dummy_622), (nb078_alpha_dummy_624 g)),
                                  ((nb078_alpha_dummy_647), (nb078_alpha_dummy_648 g)),
                                  ((nb078_alpha_dummy_645), (nb078_alpha_dummy_646 g)),
                                  ((nb078_alpha_dummy_614), (nb078_alpha_dummy_616 g)),
                                  ((nb078_alpha_dummy_613), (nb078_alpha_dummy_615 g)),
                                  ((nb078_alpha_dummy_643), (nb078_alpha_dummy_644 g)),
                                  ((nb078_alpha_dummy_617), (nb078_alpha_dummy_618 g)),
                                  ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                                  ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                                  ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                                  ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                                  ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
                                  ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
                                  ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                                  ((nb078_alpha_dummy_003), x)]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_614) ≠ (nb078_alpha_dummy_621) from (by
                            unfold nb078_alpha_dummy_621;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0636) 0))))
                        (show (nb078_alpha_dummy_616 g) ≠ (nb078_alpha_dummy_623 g) from (by
                            unfold nb078_alpha_dummy_623;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0637 g) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_614) ≠ (nb078_alpha_dummy_622) from (by
                              unfold nb078_alpha_dummy_622;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0636) 1))))
                          (show (nb078_alpha_dummy_616 g) ≠ (nb078_alpha_dummy_624 g) from (by
                              unfold nb078_alpha_dummy_624;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0637 g) 1))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_614) ≠ (nb078_alpha_dummy_647) from (by
                                unfold nb078_alpha_dummy_647;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0666) 0))))
                            (show (nb078_alpha_dummy_616 g) ≠ (nb078_alpha_dummy_648 g) from (by
                                unfold nb078_alpha_dummy_648;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0667 g) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_614) ≠ (nb078_alpha_dummy_645) from (by
                                  unfold nb078_alpha_dummy_645;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0664) 0))))
                              (show (nb078_alpha_dummy_616 g) ≠ (nb078_alpha_dummy_646 g) from
                                (by
                                  unfold nb078_alpha_dummy_646;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0665 g) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there
                        (freshVar_injective (((Class.cv (nb078_alpha_dummy_614))).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv (nb078_alpha_dummy_616 g))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078_alpha_dummy_621) ≠
        (nb078_alpha_dummy_628) from (by
          unfold nb078_alpha_dummy_628;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0640) 1)))) (show (nb078_alpha_dummy_623 g) ≠
        (nb078_alpha_dummy_631 g) from (by
          unfold nb078_alpha_dummy_631;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0641 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_621) ≠ (nb078_alpha_dummy_627) from (by
          unfold nb078_alpha_dummy_627;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0640) 0)))) (show (nb078_alpha_dummy_623 g) ≠
        (nb078_alpha_dummy_630 g) from (by
          unfold nb078_alpha_dummy_630;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0641 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_621) ≠ (nb078_alpha_dummy_625) from (by
          unfold nb078_alpha_dummy_625;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0638) 0)))) (show (nb078_alpha_dummy_623 g) ≠
        (nb078_alpha_dummy_626 g) from (by
          unfold nb078_alpha_dummy_626;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0639 g) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_629), (nb078_alpha_dummy_632 g)), ((nb078_alpha_dummy_628),
        (nb078_alpha_dummy_631 g)), ((nb078_alpha_dummy_627), (nb078_alpha_dummy_630 g)),
        ((nb078_alpha_dummy_625), (nb078_alpha_dummy_626 g)), ((nb078_alpha_dummy_621),
        (nb078_alpha_dummy_623 g)), ((nb078_alpha_dummy_622), (nb078_alpha_dummy_624 g)),
        ((nb078_alpha_dummy_647), (nb078_alpha_dummy_648 g)), ((nb078_alpha_dummy_645),
        (nb078_alpha_dummy_646 g)), ((nb078_alpha_dummy_614), (nb078_alpha_dummy_616 g)),
        ((nb078_alpha_dummy_613), (nb078_alpha_dummy_615 g)), ((nb078_alpha_dummy_643),
        (nb078_alpha_dummy_644 g)), ((nb078_alpha_dummy_617), (nb078_alpha_dummy_618 g)),
        ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570),
        (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
        ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567),
        (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_628) ≠ (nb078_alpha_dummy_635) from (by
          unfold
            nb078_alpha_dummy_635;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0644)
                  0)))) (show (nb078_alpha_dummy_631 g) ≠ (nb078_alpha_dummy_636 g) from (by
          unfold
            nb078_alpha_dummy_636;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0645
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_628) ≠ (nb078_alpha_dummy_633)
        from (by
          unfold
            nb078_alpha_dummy_633;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0642)
                  0)))) (show (nb078_alpha_dummy_631 g) ≠ (nb078_alpha_dummy_634 g) from (by
          unfold
            nb078_alpha_dummy_634;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0643
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_629) ≠ (nb078_alpha_dummy_635)
        from (by
          unfold
            nb078_alpha_dummy_635;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0648)
                  0)))) (show (nb078_alpha_dummy_632 g) ≠ (nb078_alpha_dummy_636 g) from (by
          unfold
            nb078_alpha_dummy_636;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0649
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_629) ≠ (nb078_alpha_dummy_633)
        from (by
          unfold
            nb078_alpha_dummy_633;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0646)
                  0)))) (show (nb078_alpha_dummy_632 g) ≠ (nb078_alpha_dummy_634 g) from (by
          unfold
            nb078_alpha_dummy_634;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0647
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_628) ≠ (nb078_alpha_dummy_635) from (by
          unfold
            nb078_alpha_dummy_635;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0644)
                  0)))) (show (nb078_alpha_dummy_631 g) ≠ (nb078_alpha_dummy_636 g) from (by
          unfold
            nb078_alpha_dummy_636;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0645
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_628) ≠ (nb078_alpha_dummy_633)
        from (by
          unfold
            nb078_alpha_dummy_633;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0642)
                  0)))) (show (nb078_alpha_dummy_631 g) ≠ (nb078_alpha_dummy_634 g) from (by
          unfold
            nb078_alpha_dummy_634;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0643
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_629) ≠ (nb078_alpha_dummy_635)
        from (by
          unfold
            nb078_alpha_dummy_635;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0648)
                  0)))) (show (nb078_alpha_dummy_632 g) ≠ (nb078_alpha_dummy_636 g) from (by
          unfold
            nb078_alpha_dummy_636;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0649
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_629) ≠ (nb078_alpha_dummy_633)
        from (by
          unfold
            nb078_alpha_dummy_633;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0646)
                  0)))) (show (nb078_alpha_dummy_632 g) ≠ (nb078_alpha_dummy_634 g) from (by
          unfold
            nb078_alpha_dummy_634;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0647
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_629), (nb078_alpha_dummy_632 g)), ((nb078_alpha_dummy_628),
        (nb078_alpha_dummy_631 g)), ((nb078_alpha_dummy_627), (nb078_alpha_dummy_630 g)),
        ((nb078_alpha_dummy_625), (nb078_alpha_dummy_626 g)), ((nb078_alpha_dummy_621),
        (nb078_alpha_dummy_623 g)), ((nb078_alpha_dummy_622), (nb078_alpha_dummy_624 g)),
        ((nb078_alpha_dummy_647), (nb078_alpha_dummy_648 g)), ((nb078_alpha_dummy_645),
        (nb078_alpha_dummy_646 g)), ((nb078_alpha_dummy_614), (nb078_alpha_dummy_616 g)),
        ((nb078_alpha_dummy_613), (nb078_alpha_dummy_615 g)), ((nb078_alpha_dummy_643),
        (nb078_alpha_dummy_644 g)), ((nb078_alpha_dummy_617), (nb078_alpha_dummy_618 g)),
        ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570),
        (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
        ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567),
        (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_621))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_628) ≠ (nb078_alpha_dummy_639) from (by
          unfold
            nb078_alpha_dummy_639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0652)
                  0)))) (show (nb078_alpha_dummy_631 g) ≠ (nb078_alpha_dummy_640 g) from (by
          unfold
            nb078_alpha_dummy_640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0653
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_628) ≠ (nb078_alpha_dummy_637)
        from (by
          unfold
            nb078_alpha_dummy_637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0650)
                  0)))) (show (nb078_alpha_dummy_631 g) ≠ (nb078_alpha_dummy_638 g) from (by
          unfold
            nb078_alpha_dummy_638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0651
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_628) ≠ (nb078_alpha_dummy_639)
        from (by
          unfold
            nb078_alpha_dummy_639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0652)
                  0)))) (show (nb078_alpha_dummy_631 g) ≠ (nb078_alpha_dummy_640 g) from (by
          unfold
            nb078_alpha_dummy_640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0653
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_628) ≠ (nb078_alpha_dummy_637)
        from (by
          unfold
            nb078_alpha_dummy_637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0650)
                  0)))) (show (nb078_alpha_dummy_631 g) ≠ (nb078_alpha_dummy_638 g) from (by
          unfold
            nb078_alpha_dummy_638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0651
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_629) ≠ (nb078_alpha_dummy_641) from (by
          unfold
            nb078_alpha_dummy_641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0656)
                  0)))) (show (nb078_alpha_dummy_632 g) ≠ (nb078_alpha_dummy_642 g) from (by
          unfold
            nb078_alpha_dummy_642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0657
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_629) ≠ (nb078_alpha_dummy_637)
        from (by
          unfold
            nb078_alpha_dummy_637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0654)
                  0)))) (show (nb078_alpha_dummy_632 g) ≠ (nb078_alpha_dummy_638 g) from (by
          unfold
            nb078_alpha_dummy_638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0655
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_629) ≠
        (nb078_alpha_dummy_641) from (by
          unfold
            nb078_alpha_dummy_641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0656)
                  0)))) (show (nb078_alpha_dummy_632 g) ≠ (nb078_alpha_dummy_642 g) from (by
          unfold
            nb078_alpha_dummy_642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0657
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_629) ≠ (nb078_alpha_dummy_637)
        from (by
          unfold
            nb078_alpha_dummy_637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0654)
                  0)))) (show (nb078_alpha_dummy_632 g) ≠ (nb078_alpha_dummy_638 g) from (by
          unfold
            nb078_alpha_dummy_638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0655
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_621) ≠ (nb078_alpha_dummy_625) from
                                    (by
                                      unfold nb078_alpha_dummy_625;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0638)
                                              0)))) (show
                                    (nb078_alpha_dummy_623 g) ≠ (nb078_alpha_dummy_626 g) from
                                    (by
                                      unfold nb078_alpha_dummy_626;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0639 g)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed
                                [((nb078_alpha_dummy_625), (nb078_alpha_dummy_626 g)),
                                  ((nb078_alpha_dummy_621), (nb078_alpha_dummy_623 g)),
                                  ((nb078_alpha_dummy_622), (nb078_alpha_dummy_624 g)),
                                  ((nb078_alpha_dummy_647), (nb078_alpha_dummy_648 g)),
                                  ((nb078_alpha_dummy_645), (nb078_alpha_dummy_646 g)),
                                  ((nb078_alpha_dummy_614), (nb078_alpha_dummy_616 g)),
                                  ((nb078_alpha_dummy_613), (nb078_alpha_dummy_615 g)),
                                  ((nb078_alpha_dummy_643), (nb078_alpha_dummy_644 g)),
                                  ((nb078_alpha_dummy_617), (nb078_alpha_dummy_618 g)),
                                  ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                                  ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                                  ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                                  ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                                  ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
                                  ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
                                  ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                                  ((nb078_alpha_dummy_003), x)]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb078_alpha_dummy_621) ≠ (nb078_alpha_dummy_625) from (by
                                    unfold nb078_alpha_dummy_625;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0638) 0)))) (show
                                  (nb078_alpha_dummy_623 g) ≠ (nb078_alpha_dummy_626 g) from (by
                                    unfold nb078_alpha_dummy_626;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0639 g)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_621) ≠ (nb078_alpha_dummy_625) from
                                    (by
                                      unfold nb078_alpha_dummy_625;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0638)
                                              0)))) (show
                                    (nb078_alpha_dummy_623 g) ≠ (nb078_alpha_dummy_626 g) from
                                    (by
                                      unfold nb078_alpha_dummy_626;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0639 g)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed
                                [((nb078_alpha_dummy_625), (nb078_alpha_dummy_626 g)),
                                  ((nb078_alpha_dummy_621), (nb078_alpha_dummy_623 g)),
                                  ((nb078_alpha_dummy_622), (nb078_alpha_dummy_624 g)),
                                  ((nb078_alpha_dummy_647), (nb078_alpha_dummy_648 g)),
                                  ((nb078_alpha_dummy_645), (nb078_alpha_dummy_646 g)),
                                  ((nb078_alpha_dummy_614), (nb078_alpha_dummy_616 g)),
                                  ((nb078_alpha_dummy_613), (nb078_alpha_dummy_615 g)),
                                  ((nb078_alpha_dummy_643), (nb078_alpha_dummy_644 g)),
                                  ((nb078_alpha_dummy_617), (nb078_alpha_dummy_618 g)),
                                  ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                                  ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                                  ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                                  ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                                  ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
                                  ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
                                  ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                                  ((nb078_alpha_dummy_003), x)]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part093`. -/


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
noncomputable def nb078_split_alpha_0066 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_661), (nb078_alpha_dummy_662 g)),
        ((nb078_alpha_dummy_659), (nb078_alpha_dummy_660 g)),
        ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)),
        ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
        ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)),
        ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
        ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
        ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_661))
          (Class.cab (nb078_alpha_dummy_655)
            (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_649))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_655))
                (syn_cphi (Class.cv (nb078_alpha_dummy_656))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_661)) (Class.cab (nb078_alpha_dummy_655)
              (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_649))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_655))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_656)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_662 g))
          (Class.cab (nb078_alpha_dummy_657 g)
            (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_651 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_658 g))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_662 g))
            (Class.cab (nb078_alpha_dummy_657 g)
              (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_651 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_658 g))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_649) ≠ (nb078_alpha_dummy_656) from
                    (by
                      unfold nb078_alpha_dummy_656;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0672) 1))))
                  (show (nb078_alpha_dummy_651 g) ≠ (nb078_alpha_dummy_658 g) from (by
                      unfold nb078_alpha_dummy_658;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0674 g) 1))))
                  (TAlphaVar.there (show (nb078_alpha_dummy_649) ≠ (nb078_alpha_dummy_655) from
                      (by
                        unfold nb078_alpha_dummy_655;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0672) 0))))
                    (show (nb078_alpha_dummy_651 g) ≠ (nb078_alpha_dummy_657 g) from (by
                        unfold nb078_alpha_dummy_657;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0674 g) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_649) ≠ (nb078_alpha_dummy_661) from (by
                          unfold nb078_alpha_dummy_661;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0676) 0))))
                      (show (nb078_alpha_dummy_651 g) ≠ (nb078_alpha_dummy_662 g) from (by
                          unfold nb078_alpha_dummy_662;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0677 g) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_649) ≠ (nb078_alpha_dummy_659) from (by
                            unfold nb078_alpha_dummy_659;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0673) 0))))
                        (show (nb078_alpha_dummy_651 g) ≠ (nb078_alpha_dummy_660 g) from (by
                            unfold nb078_alpha_dummy_660;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0675 g) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) (by decide))
                          (freshVar_injective (((syn_ccnv (Class.cv g))).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_649))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_650))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078_alpha_dummy_651 g))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_652 g))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_656) ≠ (nb078_alpha_dummy_663) from (by
                              unfold nb078_alpha_dummy_663;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0678) 0))))
                          (show (nb078_alpha_dummy_658 g) ≠ (nb078_alpha_dummy_665 g) from (by
                              unfold nb078_alpha_dummy_665;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0679 g) 0))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_656) ≠ (nb078_alpha_dummy_664) from (by
                                unfold nb078_alpha_dummy_664;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0678) 1))))
                            (show (nb078_alpha_dummy_658 g) ≠ (nb078_alpha_dummy_666 g) from (by
                                unfold nb078_alpha_dummy_666;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0679 g) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_656))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_658 g))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_663) ≠ (nb078_alpha_dummy_670) from (by
          unfold nb078_alpha_dummy_670;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0682) 1)))) (show (nb078_alpha_dummy_665 g) ≠
        (nb078_alpha_dummy_673 g) from (by
          unfold nb078_alpha_dummy_673;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0683 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_663) ≠ (nb078_alpha_dummy_669) from (by
          unfold nb078_alpha_dummy_669;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0682) 0)))) (show (nb078_alpha_dummy_665 g) ≠
        (nb078_alpha_dummy_672 g) from (by
          unfold nb078_alpha_dummy_672;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0683 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_663) ≠ (nb078_alpha_dummy_667) from (by
          unfold nb078_alpha_dummy_667;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0680) 0)))) (show (nb078_alpha_dummy_665 g) ≠
        (nb078_alpha_dummy_668 g) from (by
          unfold nb078_alpha_dummy_668;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0681 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_671), (nb078_alpha_dummy_674 g)), ((nb078_alpha_dummy_670),
        (nb078_alpha_dummy_673 g)), ((nb078_alpha_dummy_669), (nb078_alpha_dummy_672 g)),
        ((nb078_alpha_dummy_667), (nb078_alpha_dummy_668 g)), ((nb078_alpha_dummy_663),
        (nb078_alpha_dummy_665 g)), ((nb078_alpha_dummy_664), (nb078_alpha_dummy_666 g)),
        ((nb078_alpha_dummy_656), (nb078_alpha_dummy_658 g)), ((nb078_alpha_dummy_655),
        (nb078_alpha_dummy_657 g)), ((nb078_alpha_dummy_661), (nb078_alpha_dummy_662 g)),
        ((nb078_alpha_dummy_659), (nb078_alpha_dummy_660 g)), ((nb078_alpha_dummy_650),
        (nb078_alpha_dummy_652 g)), ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
        ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)), ((nb078_alpha_dummy_571),
        (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575),
        (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
        ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_670) ≠ (nb078_alpha_dummy_677) from (by
          unfold
            nb078_alpha_dummy_677;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0686)
                  0)))) (show (nb078_alpha_dummy_673 g) ≠ (nb078_alpha_dummy_678 g) from (by
          unfold
            nb078_alpha_dummy_678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0687
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_670) ≠ (nb078_alpha_dummy_675)
        from (by
          unfold
            nb078_alpha_dummy_675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0684)
                  0)))) (show (nb078_alpha_dummy_673 g) ≠ (nb078_alpha_dummy_676 g) from (by
          unfold
            nb078_alpha_dummy_676;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0685
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_671) ≠ (nb078_alpha_dummy_677)
        from (by
          unfold
            nb078_alpha_dummy_677;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0690)
                  0)))) (show (nb078_alpha_dummy_674 g) ≠ (nb078_alpha_dummy_678 g) from (by
          unfold
            nb078_alpha_dummy_678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0691
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_671) ≠ (nb078_alpha_dummy_675)
        from (by
          unfold
            nb078_alpha_dummy_675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0688)
                  0)))) (show (nb078_alpha_dummy_674 g) ≠ (nb078_alpha_dummy_676 g) from (by
          unfold
            nb078_alpha_dummy_676;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0689
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_670) ≠ (nb078_alpha_dummy_677) from (by
          unfold
            nb078_alpha_dummy_677;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0686)
                  0)))) (show (nb078_alpha_dummy_673 g) ≠ (nb078_alpha_dummy_678 g) from (by
          unfold
            nb078_alpha_dummy_678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0687
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_670) ≠ (nb078_alpha_dummy_675)
        from (by
          unfold
            nb078_alpha_dummy_675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0684)
                  0)))) (show (nb078_alpha_dummy_673 g) ≠ (nb078_alpha_dummy_676 g) from (by
          unfold
            nb078_alpha_dummy_676;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0685
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_671) ≠ (nb078_alpha_dummy_677)
        from (by
          unfold
            nb078_alpha_dummy_677;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0690)
                  0)))) (show (nb078_alpha_dummy_674 g) ≠ (nb078_alpha_dummy_678 g) from (by
          unfold
            nb078_alpha_dummy_678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0691
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_671) ≠ (nb078_alpha_dummy_675)
        from (by
          unfold
            nb078_alpha_dummy_675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0688)
                  0)))) (show (nb078_alpha_dummy_674 g) ≠ (nb078_alpha_dummy_676 g) from (by
          unfold
            nb078_alpha_dummy_676;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0689
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_671), (nb078_alpha_dummy_674 g)), ((nb078_alpha_dummy_670),
        (nb078_alpha_dummy_673 g)), ((nb078_alpha_dummy_669), (nb078_alpha_dummy_672 g)),
        ((nb078_alpha_dummy_667), (nb078_alpha_dummy_668 g)), ((nb078_alpha_dummy_663),
        (nb078_alpha_dummy_665 g)), ((nb078_alpha_dummy_664), (nb078_alpha_dummy_666 g)),
        ((nb078_alpha_dummy_656), (nb078_alpha_dummy_658 g)), ((nb078_alpha_dummy_655),
        (nb078_alpha_dummy_657 g)), ((nb078_alpha_dummy_661), (nb078_alpha_dummy_662 g)),
        ((nb078_alpha_dummy_659), (nb078_alpha_dummy_660 g)), ((nb078_alpha_dummy_650),
        (nb078_alpha_dummy_652 g)), ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
        ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)), ((nb078_alpha_dummy_571),
        (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575),
        (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
        ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_663))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_670) ≠
        (nb078_alpha_dummy_681) from (by
          unfold
            nb078_alpha_dummy_681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0694)
                  0)))) (show (nb078_alpha_dummy_673 g) ≠ (nb078_alpha_dummy_682 g) from (by
          unfold
            nb078_alpha_dummy_682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0695
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_670) ≠ (nb078_alpha_dummy_679)
        from (by
          unfold
            nb078_alpha_dummy_679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0692)
                  0)))) (show (nb078_alpha_dummy_673 g) ≠ (nb078_alpha_dummy_680 g) from (by
          unfold
            nb078_alpha_dummy_680;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0693
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_670) ≠ (nb078_alpha_dummy_681)
        from (by
          unfold
            nb078_alpha_dummy_681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0694)
                  0)))) (show (nb078_alpha_dummy_673 g) ≠ (nb078_alpha_dummy_682 g) from (by
          unfold
            nb078_alpha_dummy_682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0695
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_670) ≠ (nb078_alpha_dummy_679)
        from (by
          unfold
            nb078_alpha_dummy_679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0692)
                  0)))) (show (nb078_alpha_dummy_673 g) ≠ (nb078_alpha_dummy_680 g) from (by
          unfold
            nb078_alpha_dummy_680;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0693
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_671) ≠ (nb078_alpha_dummy_683) from (by
          unfold
            nb078_alpha_dummy_683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0698)
                  0)))) (show (nb078_alpha_dummy_674 g) ≠ (nb078_alpha_dummy_684 g) from (by
          unfold
            nb078_alpha_dummy_684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0699
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_671) ≠ (nb078_alpha_dummy_679)
        from (by
          unfold
            nb078_alpha_dummy_679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0696)
                  0)))) (show (nb078_alpha_dummy_674 g) ≠ (nb078_alpha_dummy_680 g) from (by
          unfold
            nb078_alpha_dummy_680;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0697
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_671) ≠
        (nb078_alpha_dummy_683) from (by
          unfold
            nb078_alpha_dummy_683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0698)
                  0)))) (show (nb078_alpha_dummy_674 g) ≠ (nb078_alpha_dummy_684 g) from (by
          unfold
            nb078_alpha_dummy_684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0699
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_671) ≠ (nb078_alpha_dummy_679)
        from (by
          unfold
            nb078_alpha_dummy_679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0696)
                  0)))) (show (nb078_alpha_dummy_674 g) ≠ (nb078_alpha_dummy_680 g) from (by
          unfold
            nb078_alpha_dummy_680;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0697
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_663) ≠ (nb078_alpha_dummy_667) from (by
                                        unfold nb078_alpha_dummy_667;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0680)
                                                0)))) (show (nb078_alpha_dummy_665 g) ≠
                                        (nb078_alpha_dummy_668 g) from (by
                                        unfold nb078_alpha_dummy_668;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0681 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_667), (nb078_alpha_dummy_668 g)),
                                    ((nb078_alpha_dummy_663), (nb078_alpha_dummy_665 g)),
                                    ((nb078_alpha_dummy_664), (nb078_alpha_dummy_666 g)),
                                    ((nb078_alpha_dummy_656), (nb078_alpha_dummy_658 g)),
                                    ((nb078_alpha_dummy_655), (nb078_alpha_dummy_657 g)),
                                    ((nb078_alpha_dummy_661), (nb078_alpha_dummy_662 g)),
                                    ((nb078_alpha_dummy_659), (nb078_alpha_dummy_660 g)),
                                    ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)),
                                    ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
                                    ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)),
                                    ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                                    ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                                    ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                                    ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                                    ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
                                    ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
                                    ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_663) ≠ (nb078_alpha_dummy_667) from
                                    (by
                                      unfold nb078_alpha_dummy_667;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0680)
                                              0)))) (show
                                    (nb078_alpha_dummy_665 g) ≠ (nb078_alpha_dummy_668 g) from
                                    (by
                                      unfold nb078_alpha_dummy_668;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0681 g)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_663) ≠ (nb078_alpha_dummy_667) from (by
                                        unfold nb078_alpha_dummy_667;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0680)
                                                0)))) (show (nb078_alpha_dummy_665 g) ≠
                                        (nb078_alpha_dummy_668 g) from (by
                                        unfold nb078_alpha_dummy_668;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0681 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_667), (nb078_alpha_dummy_668 g)),
                                    ((nb078_alpha_dummy_663), (nb078_alpha_dummy_665 g)),
                                    ((nb078_alpha_dummy_664), (nb078_alpha_dummy_666 g)),
                                    ((nb078_alpha_dummy_656), (nb078_alpha_dummy_658 g)),
                                    ((nb078_alpha_dummy_655), (nb078_alpha_dummy_657 g)),
                                    ((nb078_alpha_dummy_661), (nb078_alpha_dummy_662 g)),
                                    ((nb078_alpha_dummy_659), (nb078_alpha_dummy_660 g)),
                                    ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)),
                                    ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
                                    ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)),
                                    ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                                    ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                                    ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                                    ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                                    ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
                                    ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
                                    ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078_alpha_dummy_649) ≠ (nb078_alpha_dummy_656) from
                      (by
                        unfold nb078_alpha_dummy_656;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0672) 1))))
                    (show (nb078_alpha_dummy_651 g) ≠ (nb078_alpha_dummy_658 g) from (by
                        unfold nb078_alpha_dummy_658;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0674 g) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_649) ≠ (nb078_alpha_dummy_655) from (by
                          unfold nb078_alpha_dummy_655;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0672) 0))))
                      (show (nb078_alpha_dummy_651 g) ≠ (nb078_alpha_dummy_657 g) from (by
                          unfold nb078_alpha_dummy_657;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0674 g) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_649) ≠ (nb078_alpha_dummy_661) from (by
                            unfold nb078_alpha_dummy_661;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0676) 0))))
                        (show (nb078_alpha_dummy_651 g) ≠ (nb078_alpha_dummy_662 g) from (by
                            unfold nb078_alpha_dummy_662;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0677 g) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_649) ≠ (nb078_alpha_dummy_659) from (by
                              unfold nb078_alpha_dummy_659;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0673) 0))))
                          (show (nb078_alpha_dummy_651 g) ≠ (nb078_alpha_dummy_660 g) from (by
                              unfold nb078_alpha_dummy_660;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0675 g) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) (by decide))
                            (freshVar_injective (((syn_ccnv (Class.cv g))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078_alpha_dummy_649))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_650))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_651 g))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_652 g))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_656) ≠ (nb078_alpha_dummy_663) from (by
                                unfold nb078_alpha_dummy_663;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0678) 0))))
                            (show (nb078_alpha_dummy_658 g) ≠ (nb078_alpha_dummy_665 g) from (by
                                unfold nb078_alpha_dummy_665;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0679 g) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_656) ≠ (nb078_alpha_dummy_664) from (by
                                  unfold nb078_alpha_dummy_664;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0678) 1))))
                              (show (nb078_alpha_dummy_658 g) ≠ (nb078_alpha_dummy_666 g) from
                                (by
                                  unfold nb078_alpha_dummy_666;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0679 g) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_656))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_658 g))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_663) ≠ (nb078_alpha_dummy_670) from (by
          unfold nb078_alpha_dummy_670;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0682) 1)))) (show (nb078_alpha_dummy_665 g) ≠
        (nb078_alpha_dummy_673 g) from (by
          unfold nb078_alpha_dummy_673;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0683 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_663) ≠ (nb078_alpha_dummy_669) from (by
          unfold nb078_alpha_dummy_669;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0682) 0)))) (show (nb078_alpha_dummy_665 g) ≠
        (nb078_alpha_dummy_672 g) from (by
          unfold nb078_alpha_dummy_672;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0683 g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_663) ≠ (nb078_alpha_dummy_667)
        from (by
          unfold nb078_alpha_dummy_667;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0680)
                  0)))) (show (nb078_alpha_dummy_665 g) ≠ (nb078_alpha_dummy_668 g) from (by
          unfold nb078_alpha_dummy_668;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0681 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_671), (nb078_alpha_dummy_674 g)), ((nb078_alpha_dummy_670),
        (nb078_alpha_dummy_673 g)), ((nb078_alpha_dummy_669), (nb078_alpha_dummy_672 g)),
        ((nb078_alpha_dummy_667), (nb078_alpha_dummy_668 g)), ((nb078_alpha_dummy_663),
        (nb078_alpha_dummy_665 g)), ((nb078_alpha_dummy_664), (nb078_alpha_dummy_666 g)),
        ((nb078_alpha_dummy_656), (nb078_alpha_dummy_658 g)), ((nb078_alpha_dummy_655),
        (nb078_alpha_dummy_657 g)), ((nb078_alpha_dummy_661), (nb078_alpha_dummy_662 g)),
        ((nb078_alpha_dummy_659), (nb078_alpha_dummy_660 g)), ((nb078_alpha_dummy_650),
        (nb078_alpha_dummy_652 g)), ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
        ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)), ((nb078_alpha_dummy_571),
        (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575),
        (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
        ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_670) ≠ (nb078_alpha_dummy_677) from (by
          unfold
            nb078_alpha_dummy_677;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0686)
                  0)))) (show (nb078_alpha_dummy_673 g) ≠ (nb078_alpha_dummy_678 g) from (by
          unfold
            nb078_alpha_dummy_678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0687
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_670) ≠ (nb078_alpha_dummy_675)
        from (by
          unfold
            nb078_alpha_dummy_675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0684)
                  0)))) (show (nb078_alpha_dummy_673 g) ≠ (nb078_alpha_dummy_676 g) from (by
          unfold
            nb078_alpha_dummy_676;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0685
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_671) ≠ (nb078_alpha_dummy_677)
        from (by
          unfold
            nb078_alpha_dummy_677;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0690)
                  0)))) (show (nb078_alpha_dummy_674 g) ≠ (nb078_alpha_dummy_678 g) from (by
          unfold
            nb078_alpha_dummy_678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0691
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_671) ≠ (nb078_alpha_dummy_675)
        from (by
          unfold
            nb078_alpha_dummy_675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0688)
                  0)))) (show (nb078_alpha_dummy_674 g) ≠ (nb078_alpha_dummy_676 g) from (by
          unfold
            nb078_alpha_dummy_676;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0689
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_670) ≠ (nb078_alpha_dummy_677) from (by
          unfold
            nb078_alpha_dummy_677;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0686)
                  0)))) (show (nb078_alpha_dummy_673 g) ≠ (nb078_alpha_dummy_678 g) from (by
          unfold
            nb078_alpha_dummy_678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0687
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_670) ≠ (nb078_alpha_dummy_675)
        from (by
          unfold
            nb078_alpha_dummy_675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0684)
                  0)))) (show (nb078_alpha_dummy_673 g) ≠ (nb078_alpha_dummy_676 g) from (by
          unfold
            nb078_alpha_dummy_676;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0685
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_671) ≠ (nb078_alpha_dummy_677)
        from (by
          unfold
            nb078_alpha_dummy_677;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0690)
                  0)))) (show (nb078_alpha_dummy_674 g) ≠ (nb078_alpha_dummy_678 g) from (by
          unfold
            nb078_alpha_dummy_678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0691
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_671) ≠ (nb078_alpha_dummy_675)
        from (by
          unfold
            nb078_alpha_dummy_675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0688)
                  0)))) (show (nb078_alpha_dummy_674 g) ≠ (nb078_alpha_dummy_676 g) from (by
          unfold
            nb078_alpha_dummy_676;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0689
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_671), (nb078_alpha_dummy_674 g)), ((nb078_alpha_dummy_670),
        (nb078_alpha_dummy_673 g)), ((nb078_alpha_dummy_669), (nb078_alpha_dummy_672 g)),
        ((nb078_alpha_dummy_667), (nb078_alpha_dummy_668 g)), ((nb078_alpha_dummy_663),
        (nb078_alpha_dummy_665 g)), ((nb078_alpha_dummy_664), (nb078_alpha_dummy_666 g)),
        ((nb078_alpha_dummy_656), (nb078_alpha_dummy_658 g)), ((nb078_alpha_dummy_655),
        (nb078_alpha_dummy_657 g)), ((nb078_alpha_dummy_661), (nb078_alpha_dummy_662 g)),
        ((nb078_alpha_dummy_659), (nb078_alpha_dummy_660 g)), ((nb078_alpha_dummy_650),
        (nb078_alpha_dummy_652 g)), ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
        ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)), ((nb078_alpha_dummy_571),
        (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575),
        (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
        ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_663))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_665
        g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_670) ≠
        (nb078_alpha_dummy_681) from (by
          unfold
            nb078_alpha_dummy_681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0694)
                  0)))) (show (nb078_alpha_dummy_673 g) ≠ (nb078_alpha_dummy_682 g) from (by
          unfold
            nb078_alpha_dummy_682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0695
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_670) ≠ (nb078_alpha_dummy_679)
        from (by
          unfold
            nb078_alpha_dummy_679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0692)
                  0)))) (show (nb078_alpha_dummy_673 g) ≠ (nb078_alpha_dummy_680 g) from (by
          unfold
            nb078_alpha_dummy_680;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0693
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_670) ≠ (nb078_alpha_dummy_681)
        from (by
          unfold
            nb078_alpha_dummy_681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0694)
                  0)))) (show (nb078_alpha_dummy_673 g) ≠ (nb078_alpha_dummy_682 g) from (by
          unfold
            nb078_alpha_dummy_682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0695
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_670) ≠ (nb078_alpha_dummy_679)
        from (by
          unfold
            nb078_alpha_dummy_679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0692)
                  0)))) (show (nb078_alpha_dummy_673 g) ≠ (nb078_alpha_dummy_680 g) from (by
          unfold
            nb078_alpha_dummy_680;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0693
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_671) ≠ (nb078_alpha_dummy_683) from (by
          unfold
            nb078_alpha_dummy_683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0698)
                  0)))) (show (nb078_alpha_dummy_674 g) ≠ (nb078_alpha_dummy_684 g) from (by
          unfold
            nb078_alpha_dummy_684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0699
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_671) ≠ (nb078_alpha_dummy_679)
        from (by
          unfold
            nb078_alpha_dummy_679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0696)
                  0)))) (show (nb078_alpha_dummy_674 g) ≠ (nb078_alpha_dummy_680 g) from (by
          unfold
            nb078_alpha_dummy_680;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0697
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_671) ≠
        (nb078_alpha_dummy_683) from (by
          unfold
            nb078_alpha_dummy_683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0698)
                  0)))) (show (nb078_alpha_dummy_674 g) ≠ (nb078_alpha_dummy_684 g) from (by
          unfold
            nb078_alpha_dummy_684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0699
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_671) ≠ (nb078_alpha_dummy_679)
        from (by
          unfold
            nb078_alpha_dummy_679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0696)
                  0)))) (show (nb078_alpha_dummy_674 g) ≠ (nb078_alpha_dummy_680 g) from (by
          unfold
            nb078_alpha_dummy_680;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0697
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_663) ≠ (nb078_alpha_dummy_667) from
                                        (by
                                          unfold nb078_alpha_dummy_667;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0680)
                                                  0)))) (show (nb078_alpha_dummy_665 g) ≠
        (nb078_alpha_dummy_668 g) from (by
                                          unfold nb078_alpha_dummy_668;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0681 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_667), (nb078_alpha_dummy_668 g)),
                                      ((nb078_alpha_dummy_663), (nb078_alpha_dummy_665 g)),
                                      ((nb078_alpha_dummy_664), (nb078_alpha_dummy_666 g)),
                                      ((nb078_alpha_dummy_656), (nb078_alpha_dummy_658 g)),
                                      ((nb078_alpha_dummy_655), (nb078_alpha_dummy_657 g)),
                                      ((nb078_alpha_dummy_661), (nb078_alpha_dummy_662 g)),
                                      ((nb078_alpha_dummy_659), (nb078_alpha_dummy_660 g)),
                                      ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)),
                                      ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
                                      ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)),
                                      ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                                      ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                                      ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                                      ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                                      ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
                                      ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
                                      ((nb078_alpha_dummy_001), g),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_663) ≠ (nb078_alpha_dummy_667) from (by
                                        unfold nb078_alpha_dummy_667;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0680)
                                                0)))) (show (nb078_alpha_dummy_665 g) ≠
                                        (nb078_alpha_dummy_668 g) from (by
                                        unfold nb078_alpha_dummy_668;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0681 g)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_663) ≠ (nb078_alpha_dummy_667) from
                                        (by
                                          unfold nb078_alpha_dummy_667;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0680)
                                                  0)))) (show (nb078_alpha_dummy_665 g) ≠
        (nb078_alpha_dummy_668 g) from (by
                                          unfold nb078_alpha_dummy_668;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0681 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_667), (nb078_alpha_dummy_668 g)),
                                      ((nb078_alpha_dummy_663), (nb078_alpha_dummy_665 g)),
                                      ((nb078_alpha_dummy_664), (nb078_alpha_dummy_666 g)),
                                      ((nb078_alpha_dummy_656), (nb078_alpha_dummy_658 g)),
                                      ((nb078_alpha_dummy_655), (nb078_alpha_dummy_657 g)),
                                      ((nb078_alpha_dummy_661), (nb078_alpha_dummy_662 g)),
                                      ((nb078_alpha_dummy_659), (nb078_alpha_dummy_660 g)),
                                      ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)),
                                      ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
                                      ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)),
                                      ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                                      ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                                      ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                                      ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                                      ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
                                      ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
                                      ((nb078_alpha_dummy_001), g),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part094`. -/


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
noncomputable def nb078_split_alpha_0067 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_689), (nb078_alpha_dummy_690 g)),
        ((nb078_alpha_dummy_687), (nb078_alpha_dummy_688 g)),
        ((nb078_alpha_dummy_656), (nb078_alpha_dummy_658 g)),
        ((nb078_alpha_dummy_655), (nb078_alpha_dummy_657 g)),
        ((nb078_alpha_dummy_685), (nb078_alpha_dummy_686 g)),
        ((nb078_alpha_dummy_659), (nb078_alpha_dummy_660 g)),
        ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)),
        ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
        ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)),
        ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
        ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
        ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_689))
          (syn_cphi (Class.cv (nb078_alpha_dummy_656)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_689))
            (syn_cphi (Class.cv (nb078_alpha_dummy_656))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_690 g))
          (syn_cphi (Class.cv (nb078_alpha_dummy_658 g)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_690 g))
            (syn_cphi (Class.cv (nb078_alpha_dummy_658 g)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_656) ≠ (nb078_alpha_dummy_663) from
                    (by
                      unfold nb078_alpha_dummy_663;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0678) 0))))
                  (show (nb078_alpha_dummy_658 g) ≠ (nb078_alpha_dummy_665 g) from (by
                      unfold nb078_alpha_dummy_665;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0679 g) 0))))
                  (TAlphaVar.there (show (nb078_alpha_dummy_656) ≠ (nb078_alpha_dummy_664) from
                      (by
                        unfold nb078_alpha_dummy_664;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0678) 1))))
                    (show (nb078_alpha_dummy_658 g) ≠ (nb078_alpha_dummy_666 g) from (by
                        unfold nb078_alpha_dummy_666;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0679 g) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_656) ≠ (nb078_alpha_dummy_689) from (by
                          unfold nb078_alpha_dummy_689;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0708) 0))))
                      (show (nb078_alpha_dummy_658 g) ≠ (nb078_alpha_dummy_690 g) from (by
                          unfold nb078_alpha_dummy_690;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0709 g) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_656) ≠ (nb078_alpha_dummy_687) from (by
                            unfold nb078_alpha_dummy_687;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0706) 0))))
                        (show (nb078_alpha_dummy_658 g) ≠ (nb078_alpha_dummy_688 g) from (by
                            unfold nb078_alpha_dummy_688;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0707 g) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_656))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_658 g))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_663) ≠ (nb078_alpha_dummy_670) from (by
                                        unfold nb078_alpha_dummy_670;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0682)
                                                1)))) (show (nb078_alpha_dummy_665 g) ≠
                                        (nb078_alpha_dummy_673 g) from (by
                                        unfold nb078_alpha_dummy_673;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0683 g)
                                                1)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_663) ≠ (nb078_alpha_dummy_669) from
                                        (by
                                          unfold nb078_alpha_dummy_669;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0682)
                                                  0)))) (show (nb078_alpha_dummy_665 g) ≠
        (nb078_alpha_dummy_672 g) from (by
                                          unfold nb078_alpha_dummy_672;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0683 g) 0))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_663) ≠
        (nb078_alpha_dummy_667) from (by
          unfold nb078_alpha_dummy_667;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0680) 0)))) (show (nb078_alpha_dummy_665 g) ≠
        (nb078_alpha_dummy_668 g) from (by
          unfold nb078_alpha_dummy_668;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0681 g) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_671),
        (nb078_alpha_dummy_674 g)), ((nb078_alpha_dummy_670), (nb078_alpha_dummy_673 g)),
                                        ((nb078_alpha_dummy_669), (nb078_alpha_dummy_672 g)),
                                        ((nb078_alpha_dummy_667), (nb078_alpha_dummy_668 g)),
                                        ((nb078_alpha_dummy_663), (nb078_alpha_dummy_665 g)),
                                        ((nb078_alpha_dummy_664), (nb078_alpha_dummy_666 g)),
                                        ((nb078_alpha_dummy_689), (nb078_alpha_dummy_690 g)),
                                        ((nb078_alpha_dummy_687), (nb078_alpha_dummy_688 g)),
                                        ((nb078_alpha_dummy_656), (nb078_alpha_dummy_658 g)),
                                        ((nb078_alpha_dummy_655), (nb078_alpha_dummy_657 g)),
                                        ((nb078_alpha_dummy_685), (nb078_alpha_dummy_686 g)),
                                        ((nb078_alpha_dummy_659), (nb078_alpha_dummy_660 g)),
                                        ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)),
                                        ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
                                        ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)),
                                        ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                                        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                                        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                                        ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                                        ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
                                        ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
                                        ((nb078_alpha_dummy_001), g),
                                        ((nb078_alpha_dummy_004), y),
                                        ((nb078_alpha_dummy_003), x)]
                                      (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_670) ≠
        (nb078_alpha_dummy_677) from (by
          unfold
            nb078_alpha_dummy_677;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0686)
                  0)))) (show (nb078_alpha_dummy_673 g) ≠ (nb078_alpha_dummy_678 g) from (by
          unfold
            nb078_alpha_dummy_678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0687
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_670) ≠ (nb078_alpha_dummy_675)
        from (by
          unfold
            nb078_alpha_dummy_675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0684)
                  0)))) (show (nb078_alpha_dummy_673 g) ≠ (nb078_alpha_dummy_676 g) from (by
          unfold
            nb078_alpha_dummy_676;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0685
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_671) ≠ (nb078_alpha_dummy_677)
        from (by
          unfold
            nb078_alpha_dummy_677;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0690)
                  0)))) (show (nb078_alpha_dummy_674 g) ≠ (nb078_alpha_dummy_678 g) from (by
          unfold
            nb078_alpha_dummy_678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0691
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_671) ≠ (nb078_alpha_dummy_675)
        from (by
          unfold
            nb078_alpha_dummy_675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0688)
                  0)))) (show (nb078_alpha_dummy_674 g) ≠ (nb078_alpha_dummy_676 g) from (by
          unfold
            nb078_alpha_dummy_676;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0689
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_670) ≠ (nb078_alpha_dummy_677) from (by
          unfold
            nb078_alpha_dummy_677;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0686)
                  0)))) (show (nb078_alpha_dummy_673 g) ≠ (nb078_alpha_dummy_678 g) from (by
          unfold
            nb078_alpha_dummy_678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0687
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_670) ≠ (nb078_alpha_dummy_675)
        from (by
          unfold
            nb078_alpha_dummy_675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0684)
                  0)))) (show (nb078_alpha_dummy_673 g) ≠ (nb078_alpha_dummy_676 g) from (by
          unfold
            nb078_alpha_dummy_676;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0685
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_671) ≠ (nb078_alpha_dummy_677)
        from (by
          unfold
            nb078_alpha_dummy_677;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0690)
                  0)))) (show (nb078_alpha_dummy_674 g) ≠ (nb078_alpha_dummy_678 g) from (by
          unfold
            nb078_alpha_dummy_678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0691
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_671) ≠ (nb078_alpha_dummy_675)
        from (by
          unfold
            nb078_alpha_dummy_675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0688)
                  0)))) (show (nb078_alpha_dummy_674 g) ≠ (nb078_alpha_dummy_676 g) from (by
          unfold
            nb078_alpha_dummy_676;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0689
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb078_alpha_dummy_671), (nb078_alpha_dummy_674 g)),
        ((nb078_alpha_dummy_670), (nb078_alpha_dummy_673 g)), ((nb078_alpha_dummy_669),
        (nb078_alpha_dummy_672 g)), ((nb078_alpha_dummy_667), (nb078_alpha_dummy_668 g)),
        ((nb078_alpha_dummy_663), (nb078_alpha_dummy_665 g)), ((nb078_alpha_dummy_664),
        (nb078_alpha_dummy_666 g)), ((nb078_alpha_dummy_689), (nb078_alpha_dummy_690 g)),
        ((nb078_alpha_dummy_687), (nb078_alpha_dummy_688 g)), ((nb078_alpha_dummy_656),
        (nb078_alpha_dummy_658 g)), ((nb078_alpha_dummy_655), (nb078_alpha_dummy_657 g)),
        ((nb078_alpha_dummy_685), (nb078_alpha_dummy_686 g)), ((nb078_alpha_dummy_659),
        (nb078_alpha_dummy_660 g)), ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)),
        ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)), ((nb078_alpha_dummy_653),
        (nb078_alpha_dummy_654 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569),
        (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565),
        (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_670) ≠
        (nb078_alpha_dummy_681) from (by
          unfold
            nb078_alpha_dummy_681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0694)
                  0)))) (show (nb078_alpha_dummy_673 g) ≠ (nb078_alpha_dummy_682 g) from (by
          unfold
            nb078_alpha_dummy_682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0695
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_670) ≠ (nb078_alpha_dummy_679)
        from (by
          unfold
            nb078_alpha_dummy_679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0692)
                  0)))) (show (nb078_alpha_dummy_673 g) ≠ (nb078_alpha_dummy_680 g) from (by
          unfold
            nb078_alpha_dummy_680;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0693
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_670) ≠ (nb078_alpha_dummy_681)
        from (by
          unfold
            nb078_alpha_dummy_681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0694)
                  0)))) (show (nb078_alpha_dummy_673 g) ≠ (nb078_alpha_dummy_682 g) from (by
          unfold
            nb078_alpha_dummy_682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0695
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_670) ≠ (nb078_alpha_dummy_679)
        from (by
          unfold
            nb078_alpha_dummy_679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0692)
                  0)))) (show (nb078_alpha_dummy_673 g) ≠ (nb078_alpha_dummy_680 g) from (by
          unfold
            nb078_alpha_dummy_680;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0693
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_671) ≠ (nb078_alpha_dummy_683) from (by
          unfold
            nb078_alpha_dummy_683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0698)
                  0)))) (show (nb078_alpha_dummy_674 g) ≠ (nb078_alpha_dummy_684 g) from (by
          unfold
            nb078_alpha_dummy_684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0699
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_671) ≠ (nb078_alpha_dummy_679)
        from (by
          unfold
            nb078_alpha_dummy_679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0696)
                  0)))) (show (nb078_alpha_dummy_674 g) ≠ (nb078_alpha_dummy_680 g) from (by
          unfold
            nb078_alpha_dummy_680;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0697
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_671) ≠
        (nb078_alpha_dummy_683) from (by
          unfold
            nb078_alpha_dummy_683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0698)
                  0)))) (show (nb078_alpha_dummy_674 g) ≠ (nb078_alpha_dummy_684 g) from (by
          unfold
            nb078_alpha_dummy_684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0699
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_671) ≠ (nb078_alpha_dummy_679)
        from (by
          unfold
            nb078_alpha_dummy_679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0696)
                  0)))) (show (nb078_alpha_dummy_674 g) ≠ (nb078_alpha_dummy_680 g) from (by
          unfold
            nb078_alpha_dummy_680;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0697
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_663) ≠ (nb078_alpha_dummy_667) from (by
                                unfold nb078_alpha_dummy_667;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0680) 0))))
                            (show (nb078_alpha_dummy_665 g) ≠ (nb078_alpha_dummy_668 g) from (by
                                unfold nb078_alpha_dummy_668;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0681 g) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb078_alpha_dummy_667), (nb078_alpha_dummy_668 g)),
                            ((nb078_alpha_dummy_663), (nb078_alpha_dummy_665 g)),
                            ((nb078_alpha_dummy_664), (nb078_alpha_dummy_666 g)),
                            ((nb078_alpha_dummy_689), (nb078_alpha_dummy_690 g)),
                            ((nb078_alpha_dummy_687), (nb078_alpha_dummy_688 g)),
                            ((nb078_alpha_dummy_656), (nb078_alpha_dummy_658 g)),
                            ((nb078_alpha_dummy_655), (nb078_alpha_dummy_657 g)),
                            ((nb078_alpha_dummy_685), (nb078_alpha_dummy_686 g)),
                            ((nb078_alpha_dummy_659), (nb078_alpha_dummy_660 g)),
                            ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)),
                            ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
                            ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)),
                            ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                            ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                            ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                            ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                            ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
                            ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
                            ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                            ((nb078_alpha_dummy_003), x)]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_663) ≠ (nb078_alpha_dummy_667) from (by
                              unfold nb078_alpha_dummy_667;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0680) 0))))
                          (show (nb078_alpha_dummy_665 g) ≠ (nb078_alpha_dummy_668 g) from (by
                              unfold nb078_alpha_dummy_668;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0681 g) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_663) ≠ (nb078_alpha_dummy_667) from (by
                                unfold nb078_alpha_dummy_667;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0680) 0))))
                            (show (nb078_alpha_dummy_665 g) ≠ (nb078_alpha_dummy_668 g) from (by
                                unfold nb078_alpha_dummy_668;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0681 g) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb078_alpha_dummy_667), (nb078_alpha_dummy_668 g)),
                            ((nb078_alpha_dummy_663), (nb078_alpha_dummy_665 g)),
                            ((nb078_alpha_dummy_664), (nb078_alpha_dummy_666 g)),
                            ((nb078_alpha_dummy_689), (nb078_alpha_dummy_690 g)),
                            ((nb078_alpha_dummy_687), (nb078_alpha_dummy_688 g)),
                            ((nb078_alpha_dummy_656), (nb078_alpha_dummy_658 g)),
                            ((nb078_alpha_dummy_655), (nb078_alpha_dummy_657 g)),
                            ((nb078_alpha_dummy_685), (nb078_alpha_dummy_686 g)),
                            ((nb078_alpha_dummy_659), (nb078_alpha_dummy_660 g)),
                            ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)),
                            ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
                            ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)),
                            ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                            ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                            ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                            ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                            ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
                            ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
                            ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                            ((nb078_alpha_dummy_003), x)]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb078_alpha_dummy_656) ≠ (nb078_alpha_dummy_663) from (by
                        unfold nb078_alpha_dummy_663;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0678) 0))))
                    (show (nb078_alpha_dummy_658 g) ≠ (nb078_alpha_dummy_665 g) from (by
                        unfold nb078_alpha_dummy_665;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0679 g) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_656) ≠ (nb078_alpha_dummy_664) from (by
                          unfold nb078_alpha_dummy_664;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0678) 1))))
                      (show (nb078_alpha_dummy_658 g) ≠ (nb078_alpha_dummy_666 g) from (by
                          unfold nb078_alpha_dummy_666;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0679 g) 1))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_656) ≠ (nb078_alpha_dummy_689) from (by
                            unfold nb078_alpha_dummy_689;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0708) 0))))
                        (show (nb078_alpha_dummy_658 g) ≠ (nb078_alpha_dummy_690 g) from (by
                            unfold nb078_alpha_dummy_690;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0709 g) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_656) ≠ (nb078_alpha_dummy_687) from (by
                              unfold nb078_alpha_dummy_687;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0706) 0))))
                          (show (nb078_alpha_dummy_658 g) ≠ (nb078_alpha_dummy_688 g) from (by
                              unfold nb078_alpha_dummy_688;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0707 g) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_656))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_658 g))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb078_alpha_dummy_663) ≠ (nb078_alpha_dummy_670) from
                                        (by
                                          unfold nb078_alpha_dummy_670;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0682)
                                                  1)))) (show (nb078_alpha_dummy_665 g) ≠
        (nb078_alpha_dummy_673 g) from (by
                                          unfold nb078_alpha_dummy_673;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0683 g) 1))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_663) ≠
        (nb078_alpha_dummy_669) from (by
          unfold nb078_alpha_dummy_669;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0682) 0)))) (show (nb078_alpha_dummy_665 g) ≠
        (nb078_alpha_dummy_672 g) from (by
          unfold nb078_alpha_dummy_672;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0683 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_663) ≠ (nb078_alpha_dummy_667) from (by
          unfold nb078_alpha_dummy_667;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0680) 0)))) (show (nb078_alpha_dummy_665 g) ≠
        (nb078_alpha_dummy_668 g) from (by
          unfold nb078_alpha_dummy_668;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0681 g) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_671),
        (nb078_alpha_dummy_674 g)), ((nb078_alpha_dummy_670), (nb078_alpha_dummy_673 g)),
        ((nb078_alpha_dummy_669), (nb078_alpha_dummy_672 g)), ((nb078_alpha_dummy_667),
        (nb078_alpha_dummy_668 g)), ((nb078_alpha_dummy_663), (nb078_alpha_dummy_665 g)),
        ((nb078_alpha_dummy_664), (nb078_alpha_dummy_666 g)), ((nb078_alpha_dummy_689),
        (nb078_alpha_dummy_690 g)), ((nb078_alpha_dummy_687), (nb078_alpha_dummy_688 g)),
        ((nb078_alpha_dummy_656), (nb078_alpha_dummy_658 g)), ((nb078_alpha_dummy_655),
        (nb078_alpha_dummy_657 g)), ((nb078_alpha_dummy_685), (nb078_alpha_dummy_686 g)),
        ((nb078_alpha_dummy_659), (nb078_alpha_dummy_660 g)), ((nb078_alpha_dummy_650),
        (nb078_alpha_dummy_652 g)), ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
        ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)), ((nb078_alpha_dummy_571),
        (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575),
        (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
        ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
                                        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_670) ≠
        (nb078_alpha_dummy_677) from (by
          unfold
            nb078_alpha_dummy_677;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0686)
                  0)))) (show (nb078_alpha_dummy_673 g) ≠ (nb078_alpha_dummy_678 g) from (by
          unfold
            nb078_alpha_dummy_678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0687
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_670) ≠ (nb078_alpha_dummy_675)
        from (by
          unfold
            nb078_alpha_dummy_675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0684)
                  0)))) (show (nb078_alpha_dummy_673 g) ≠ (nb078_alpha_dummy_676 g) from (by
          unfold
            nb078_alpha_dummy_676;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0685
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_671) ≠ (nb078_alpha_dummy_677)
        from (by
          unfold
            nb078_alpha_dummy_677;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0690)
                  0)))) (show (nb078_alpha_dummy_674 g) ≠ (nb078_alpha_dummy_678 g) from (by
          unfold
            nb078_alpha_dummy_678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0691
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_671) ≠ (nb078_alpha_dummy_675)
        from (by
          unfold
            nb078_alpha_dummy_675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0688)
                  0)))) (show (nb078_alpha_dummy_674 g) ≠ (nb078_alpha_dummy_676 g) from (by
          unfold
            nb078_alpha_dummy_676;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0689
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_670) ≠ (nb078_alpha_dummy_677) from (by
          unfold
            nb078_alpha_dummy_677;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0686)
                  0)))) (show (nb078_alpha_dummy_673 g) ≠ (nb078_alpha_dummy_678 g) from (by
          unfold
            nb078_alpha_dummy_678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0687
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_670) ≠ (nb078_alpha_dummy_675)
        from (by
          unfold
            nb078_alpha_dummy_675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0684)
                  0)))) (show (nb078_alpha_dummy_673 g) ≠ (nb078_alpha_dummy_676 g) from (by
          unfold
            nb078_alpha_dummy_676;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0685
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_671) ≠ (nb078_alpha_dummy_677)
        from (by
          unfold
            nb078_alpha_dummy_677;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0690)
                  0)))) (show (nb078_alpha_dummy_674 g) ≠ (nb078_alpha_dummy_678 g) from (by
          unfold
            nb078_alpha_dummy_678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0691
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_671) ≠ (nb078_alpha_dummy_675)
        from (by
          unfold
            nb078_alpha_dummy_675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0688)
                  0)))) (show (nb078_alpha_dummy_674 g) ≠ (nb078_alpha_dummy_676 g) from (by
          unfold
            nb078_alpha_dummy_676;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0689
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_671), (nb078_alpha_dummy_674 g)), ((nb078_alpha_dummy_670),
        (nb078_alpha_dummy_673 g)), ((nb078_alpha_dummy_669), (nb078_alpha_dummy_672 g)),
        ((nb078_alpha_dummy_667), (nb078_alpha_dummy_668 g)), ((nb078_alpha_dummy_663),
        (nb078_alpha_dummy_665 g)), ((nb078_alpha_dummy_664), (nb078_alpha_dummy_666 g)),
        ((nb078_alpha_dummy_689), (nb078_alpha_dummy_690 g)), ((nb078_alpha_dummy_687),
        (nb078_alpha_dummy_688 g)), ((nb078_alpha_dummy_656), (nb078_alpha_dummy_658 g)),
        ((nb078_alpha_dummy_655), (nb078_alpha_dummy_657 g)), ((nb078_alpha_dummy_685),
        (nb078_alpha_dummy_686 g)), ((nb078_alpha_dummy_659), (nb078_alpha_dummy_660 g)),
        ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)), ((nb078_alpha_dummy_649),
        (nb078_alpha_dummy_651 g)), ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)),
        ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570),
        (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
        ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567),
        (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_670) ≠
        (nb078_alpha_dummy_681) from (by
          unfold
            nb078_alpha_dummy_681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0694)
                  0)))) (show (nb078_alpha_dummy_673 g) ≠ (nb078_alpha_dummy_682 g) from (by
          unfold
            nb078_alpha_dummy_682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0695
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_670) ≠ (nb078_alpha_dummy_679)
        from (by
          unfold
            nb078_alpha_dummy_679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0692)
                  0)))) (show (nb078_alpha_dummy_673 g) ≠ (nb078_alpha_dummy_680 g) from (by
          unfold
            nb078_alpha_dummy_680;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0693
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_670) ≠ (nb078_alpha_dummy_681)
        from (by
          unfold
            nb078_alpha_dummy_681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0694)
                  0)))) (show (nb078_alpha_dummy_673 g) ≠ (nb078_alpha_dummy_682 g) from (by
          unfold
            nb078_alpha_dummy_682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0695
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_670) ≠ (nb078_alpha_dummy_679)
        from (by
          unfold
            nb078_alpha_dummy_679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0692)
                  0)))) (show (nb078_alpha_dummy_673 g) ≠ (nb078_alpha_dummy_680 g) from (by
          unfold
            nb078_alpha_dummy_680;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0693
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_671) ≠ (nb078_alpha_dummy_683) from (by
          unfold
            nb078_alpha_dummy_683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0698)
                  0)))) (show (nb078_alpha_dummy_674 g) ≠ (nb078_alpha_dummy_684 g) from (by
          unfold
            nb078_alpha_dummy_684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0699
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_671) ≠ (nb078_alpha_dummy_679)
        from (by
          unfold
            nb078_alpha_dummy_679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0696)
                  0)))) (show (nb078_alpha_dummy_674 g) ≠ (nb078_alpha_dummy_680 g) from (by
          unfold
            nb078_alpha_dummy_680;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0697
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_671) ≠
        (nb078_alpha_dummy_683) from (by
          unfold
            nb078_alpha_dummy_683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0698)
                  0)))) (show (nb078_alpha_dummy_674 g) ≠ (nb078_alpha_dummy_684 g) from (by
          unfold
            nb078_alpha_dummy_684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0699
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_671) ≠ (nb078_alpha_dummy_679)
        from (by
          unfold
            nb078_alpha_dummy_679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0696)
                  0)))) (show (nb078_alpha_dummy_674 g) ≠ (nb078_alpha_dummy_680 g) from (by
          unfold
            nb078_alpha_dummy_680;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0697
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078_alpha_dummy_663) ≠ (nb078_alpha_dummy_667) from (by
                                  unfold nb078_alpha_dummy_667;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0680) 0))))
                              (show (nb078_alpha_dummy_665 g) ≠ (nb078_alpha_dummy_668 g) from
                                (by
                                  unfold nb078_alpha_dummy_668;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0681 g) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb078_alpha_dummy_667), (nb078_alpha_dummy_668 g)),
                              ((nb078_alpha_dummy_663), (nb078_alpha_dummy_665 g)),
                              ((nb078_alpha_dummy_664), (nb078_alpha_dummy_666 g)),
                              ((nb078_alpha_dummy_689), (nb078_alpha_dummy_690 g)),
                              ((nb078_alpha_dummy_687), (nb078_alpha_dummy_688 g)),
                              ((nb078_alpha_dummy_656), (nb078_alpha_dummy_658 g)),
                              ((nb078_alpha_dummy_655), (nb078_alpha_dummy_657 g)),
                              ((nb078_alpha_dummy_685), (nb078_alpha_dummy_686 g)),
                              ((nb078_alpha_dummy_659), (nb078_alpha_dummy_660 g)),
                              ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)),
                              ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
                              ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)),
                              ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                              ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                              ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                              ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                              ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
                              ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
                              ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                              ((nb078_alpha_dummy_003), x)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_663) ≠ (nb078_alpha_dummy_667) from (by
                                unfold nb078_alpha_dummy_667;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0680) 0))))
                            (show (nb078_alpha_dummy_665 g) ≠ (nb078_alpha_dummy_668 g) from (by
                                unfold nb078_alpha_dummy_668;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0681 g) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078_alpha_dummy_663) ≠ (nb078_alpha_dummy_667) from (by
                                  unfold nb078_alpha_dummy_667;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0680) 0))))
                              (show (nb078_alpha_dummy_665 g) ≠ (nb078_alpha_dummy_668 g) from
                                (by
                                  unfold nb078_alpha_dummy_668;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0681 g) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb078_alpha_dummy_667), (nb078_alpha_dummy_668 g)),
                              ((nb078_alpha_dummy_663), (nb078_alpha_dummy_665 g)),
                              ((nb078_alpha_dummy_664), (nb078_alpha_dummy_666 g)),
                              ((nb078_alpha_dummy_689), (nb078_alpha_dummy_690 g)),
                              ((nb078_alpha_dummy_687), (nb078_alpha_dummy_688 g)),
                              ((nb078_alpha_dummy_656), (nb078_alpha_dummy_658 g)),
                              ((nb078_alpha_dummy_655), (nb078_alpha_dummy_657 g)),
                              ((nb078_alpha_dummy_685), (nb078_alpha_dummy_686 g)),
                              ((nb078_alpha_dummy_659), (nb078_alpha_dummy_660 g)),
                              ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)),
                              ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
                              ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)),
                              ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                              ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                              ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                              ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                              ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
                              ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
                              ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                              ((nb078_alpha_dummy_003), x)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
