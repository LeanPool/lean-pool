/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block026

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part087`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0059`. -/
@[expose]
noncomputable def nb078SplitAlpha0059 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078AlphaDummy561), (nb078AlphaDummy562 g)),
        ((nb078AlphaDummy530), (nb078AlphaDummy532 g)),
        ((nb078AlphaDummy529), (nb078AlphaDummy531 g)),
        ((nb078AlphaDummy559), (nb078AlphaDummy560 g)),
        ((nb078AlphaDummy533), (nb078AlphaDummy534 g)),
        ((nb078AlphaDummy526), (nb078AlphaDummy528 g)),
        ((nb078AlphaDummy525), (nb078AlphaDummy527 g)),
        ((nb078AlphaDummy523), (nb078AlphaDummy524 x g)),
        ((nb078AlphaDummy521), (nb078AlphaDummy522 x g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.neg (synWa (Wff.classMem (Class.cv (nb078AlphaDummy561))
            (synCcompl (synCphi (Class.cv (nb078AlphaDummy530)))))
          (Wff.classMem (Class.cv (nb078AlphaDummy561)) (synCcompl (synCsn (synC0c))))))
      (Wff.neg (synWa (Wff.classMem (Class.cv (nb078AlphaDummy562 g))
            (synCcompl (synCphi (Class.cv (nb078AlphaDummy532 g)))))
          (Wff.classMem (Class.cv (nb078AlphaDummy562 g))
            (synCcompl (synCsn (synC0c)))))) :=
  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy530) ≠ (nb078AlphaDummy537) from (by
                                unfold nb078AlphaDummy537;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0546) 0))))
                            (show (nb078AlphaDummy532 g) ≠ (nb078AlphaDummy539 g) from (by
                                unfold nb078AlphaDummy539;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0547 g) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy530) ≠ (nb078AlphaDummy538) from (by
                                  unfold nb078AlphaDummy538;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0546) 1))))
                              (show (nb078AlphaDummy532 g) ≠ (nb078AlphaDummy540 g) from
                                (by
                                  unfold nb078AlphaDummy540;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0547 g) 1))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy530) ≠ (nb078AlphaDummy563) from (by
                                    unfold nb078AlphaDummy563;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0576) 0)))) (show
                                  (nb078AlphaDummy532 g) ≠ (nb078AlphaDummy564 g) from (by
                                    unfold nb078AlphaDummy564;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0577 g)
                                            0)))) (TAlphaVar.there
                                  (show (nb078AlphaDummy530) ≠ (nb078AlphaDummy561) from
                                    (by
                                      unfold nb078AlphaDummy561;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0574)
                                              0)))) (show
                                    (nb078AlphaDummy532 g) ≠ (nb078AlphaDummy562 g) from
                                    (by
                                      unfold nb078AlphaDummy562;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0575 g)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy530))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy532 g))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy537) ≠ (nb078AlphaDummy544) from (by
          unfold nb078AlphaDummy544;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0550) 1)))) (show (nb078AlphaDummy539 g) ≠
        (nb078AlphaDummy547 g) from (by
          unfold nb078AlphaDummy547;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0551 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy537) ≠ (nb078AlphaDummy543) from (by
          unfold nb078AlphaDummy543;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0550) 0)))) (show (nb078AlphaDummy539 g) ≠
        (nb078AlphaDummy546 g) from (by
          unfold nb078AlphaDummy546;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0551 g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy537) ≠ (nb078AlphaDummy541)
        from (by
          unfold nb078AlphaDummy541;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0548)
                  0)))) (show (nb078AlphaDummy539 g) ≠ (nb078AlphaDummy542 g) from (by
          unfold nb078AlphaDummy542;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0549 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy545), (nb078AlphaDummy548 g)), ((nb078AlphaDummy544),
        (nb078AlphaDummy547 g)), ((nb078AlphaDummy543), (nb078AlphaDummy546 g)),
        ((nb078AlphaDummy541), (nb078AlphaDummy542 g)), ((nb078AlphaDummy537),
        (nb078AlphaDummy539 g)), ((nb078AlphaDummy538), (nb078AlphaDummy540 g)),
        ((nb078AlphaDummy563), (nb078AlphaDummy564 g)), ((nb078AlphaDummy561),
        (nb078AlphaDummy562 g)), ((nb078AlphaDummy530), (nb078AlphaDummy532 g)),
        ((nb078AlphaDummy529), (nb078AlphaDummy531 g)), ((nb078AlphaDummy559),
        (nb078AlphaDummy560 g)), ((nb078AlphaDummy533), (nb078AlphaDummy534 g)),
        ((nb078AlphaDummy526), (nb078AlphaDummy528 g)), ((nb078AlphaDummy525),
        (nb078AlphaDummy527 g)), ((nb078AlphaDummy523), (nb078AlphaDummy524 x g)),
        ((nb078AlphaDummy521), (nb078AlphaDummy522 x g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy551) from (by
          unfold
            nb078AlphaDummy551;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0554)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy552 g) from (by
          unfold
            nb078AlphaDummy552;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0555
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy549)
        from (by
          unfold
            nb078AlphaDummy549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0552)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy550 g) from (by
          unfold
            nb078AlphaDummy550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0553
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy539 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy551)
        from (by
          unfold
            nb078AlphaDummy551;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0558)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy552 g) from (by
          unfold
            nb078AlphaDummy552;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0559
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy549)
        from (by
          unfold
            nb078AlphaDummy549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0556)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy550 g) from (by
          unfold
            nb078AlphaDummy550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0557
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy551) from (by
          unfold
            nb078AlphaDummy551;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0554)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy552 g) from (by
          unfold
            nb078AlphaDummy552;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0555
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy549)
        from (by
          unfold
            nb078AlphaDummy549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0552)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy550 g) from (by
          unfold
            nb078AlphaDummy550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0553
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy539 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy551)
        from (by
          unfold
            nb078AlphaDummy551;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0558)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy552 g) from (by
          unfold
            nb078AlphaDummy552;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0559
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy549)
        from (by
          unfold
            nb078AlphaDummy549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0556)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy550 g) from (by
          unfold
            nb078AlphaDummy550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0557
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy545), (nb078AlphaDummy548 g)), ((nb078AlphaDummy544),
        (nb078AlphaDummy547 g)), ((nb078AlphaDummy543), (nb078AlphaDummy546 g)),
        ((nb078AlphaDummy541), (nb078AlphaDummy542 g)), ((nb078AlphaDummy537),
        (nb078AlphaDummy539 g)), ((nb078AlphaDummy538), (nb078AlphaDummy540 g)),
        ((nb078AlphaDummy563), (nb078AlphaDummy564 g)), ((nb078AlphaDummy561),
        (nb078AlphaDummy562 g)), ((nb078AlphaDummy530), (nb078AlphaDummy532 g)),
        ((nb078AlphaDummy529), (nb078AlphaDummy531 g)), ((nb078AlphaDummy559),
        (nb078AlphaDummy560 g)), ((nb078AlphaDummy533), (nb078AlphaDummy534 g)),
        ((nb078AlphaDummy526), (nb078AlphaDummy528 g)), ((nb078AlphaDummy525),
        (nb078AlphaDummy527 g)), ((nb078AlphaDummy523), (nb078AlphaDummy524 x g)),
        ((nb078AlphaDummy521), (nb078AlphaDummy522 x g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy537))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy539
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy539 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy544) ≠
        (nb078AlphaDummy555) from (by
          unfold
            nb078AlphaDummy555;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0562)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy556 g) from (by
          unfold
            nb078AlphaDummy556;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0563
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy553)
        from (by
          unfold
            nb078AlphaDummy553;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0560)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy554 g) from (by
          unfold
            nb078AlphaDummy554;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0561
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy539 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy555)
        from (by
          unfold
            nb078AlphaDummy555;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0562)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy556 g) from (by
          unfold
            nb078AlphaDummy556;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0563
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy553)
        from (by
          unfold
            nb078AlphaDummy553;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0560)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy554 g) from (by
          unfold
            nb078AlphaDummy554;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0561
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy539 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy557) from (by
          unfold
            nb078AlphaDummy557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0566)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy558 g) from (by
          unfold
            nb078AlphaDummy558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0567
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy553)
        from (by
          unfold
            nb078AlphaDummy553;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0564)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy554 g) from (by
          unfold
            nb078AlphaDummy554;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0565
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy545) ≠
        (nb078AlphaDummy557) from (by
          unfold
            nb078AlphaDummy557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0566)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy558 g) from (by
          unfold
            nb078AlphaDummy558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0567
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy553)
        from (by
          unfold
            nb078AlphaDummy553;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0564)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy554 g) from (by
          unfold
            nb078AlphaDummy554;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0565
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy537) ≠ (nb078AlphaDummy541) from
                                        (by
                                          unfold nb078AlphaDummy541;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0548)
                                                  0)))) (show (nb078AlphaDummy539 g) ≠
        (nb078AlphaDummy542 g) from (by
                                          unfold nb078AlphaDummy542;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0549 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy541), (nb078AlphaDummy542 g)),
                                      ((nb078AlphaDummy537), (nb078AlphaDummy539 g)),
                                      ((nb078AlphaDummy538), (nb078AlphaDummy540 g)),
                                      ((nb078AlphaDummy563), (nb078AlphaDummy564 g)),
                                      ((nb078AlphaDummy561), (nb078AlphaDummy562 g)),
                                      ((nb078AlphaDummy530), (nb078AlphaDummy532 g)),
                                      ((nb078AlphaDummy529), (nb078AlphaDummy531 g)),
                                      ((nb078AlphaDummy559), (nb078AlphaDummy560 g)),
                                      ((nb078AlphaDummy533), (nb078AlphaDummy534 g)),
                                      ((nb078AlphaDummy526), (nb078AlphaDummy528 g)),
                                      ((nb078AlphaDummy525), (nb078AlphaDummy527 g)),
                                      ((nb078AlphaDummy523), (nb078AlphaDummy524 x g)),
                                      ((nb078AlphaDummy521), (nb078AlphaDummy522 x g)),
                                      ((nb078AlphaDummy001), g),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy537) ≠ (nb078AlphaDummy541) from (by
                                        unfold nb078AlphaDummy541;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0548)
                                                0)))) (show (nb078AlphaDummy539 g) ≠
                                        (nb078AlphaDummy542 g) from (by
                                        unfold nb078AlphaDummy542;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0549 g)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy537) ≠ (nb078AlphaDummy541) from
                                        (by
                                          unfold nb078AlphaDummy541;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0548)
                                                  0)))) (show (nb078AlphaDummy539 g) ≠
        (nb078AlphaDummy542 g) from (by
                                          unfold nb078AlphaDummy542;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0549 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy541), (nb078AlphaDummy542 g)),
                                      ((nb078AlphaDummy537), (nb078AlphaDummy539 g)),
                                      ((nb078AlphaDummy538), (nb078AlphaDummy540 g)),
                                      ((nb078AlphaDummy563), (nb078AlphaDummy564 g)),
                                      ((nb078AlphaDummy561), (nb078AlphaDummy562 g)),
                                      ((nb078AlphaDummy530), (nb078AlphaDummy532 g)),
                                      ((nb078AlphaDummy529), (nb078AlphaDummy531 g)),
                                      ((nb078AlphaDummy559), (nb078AlphaDummy560 g)),
                                      ((nb078AlphaDummy533), (nb078AlphaDummy534 g)),
                                      ((nb078AlphaDummy526), (nb078AlphaDummy528 g)),
                                      ((nb078AlphaDummy525), (nb078AlphaDummy527 g)),
                                      ((nb078AlphaDummy523), (nb078AlphaDummy524 x g)),
                                      ((nb078AlphaDummy521), (nb078AlphaDummy522 x g)),
                                      ((nb078AlphaDummy001), g),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy530) ≠ (nb078AlphaDummy537) from (by
                                unfold nb078AlphaDummy537;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0546) 0))))
                            (show (nb078AlphaDummy532 g) ≠ (nb078AlphaDummy539 g) from (by
                                unfold nb078AlphaDummy539;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0547 g) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy530) ≠ (nb078AlphaDummy538) from (by
                                  unfold nb078AlphaDummy538;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0546) 1))))
                              (show (nb078AlphaDummy532 g) ≠ (nb078AlphaDummy540 g) from
                                (by
                                  unfold nb078AlphaDummy540;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0547 g) 1))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy530) ≠ (nb078AlphaDummy563) from (by
                                    unfold nb078AlphaDummy563;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0576) 0)))) (show
                                  (nb078AlphaDummy532 g) ≠ (nb078AlphaDummy564 g) from (by
                                    unfold nb078AlphaDummy564;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0577 g)
                                            0)))) (TAlphaVar.there
                                  (show (nb078AlphaDummy530) ≠ (nb078AlphaDummy561) from
                                    (by
                                      unfold nb078AlphaDummy561;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0574)
                                              0)))) (show
                                    (nb078AlphaDummy532 g) ≠ (nb078AlphaDummy562 g) from
                                    (by
                                      unfold nb078AlphaDummy562;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0575 g)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy530))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy532 g))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy537) ≠ (nb078AlphaDummy544) from (by
          unfold nb078AlphaDummy544;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0550) 1)))) (show (nb078AlphaDummy539 g) ≠
        (nb078AlphaDummy547 g) from (by
          unfold nb078AlphaDummy547;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0551 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy537) ≠ (nb078AlphaDummy543) from (by
          unfold nb078AlphaDummy543;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0550) 0)))) (show (nb078AlphaDummy539 g) ≠
        (nb078AlphaDummy546 g) from (by
          unfold nb078AlphaDummy546;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0551 g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy537) ≠ (nb078AlphaDummy541)
        from (by
          unfold nb078AlphaDummy541;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0548)
                  0)))) (show (nb078AlphaDummy539 g) ≠ (nb078AlphaDummy542 g) from (by
          unfold nb078AlphaDummy542;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0549 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy545), (nb078AlphaDummy548 g)), ((nb078AlphaDummy544),
        (nb078AlphaDummy547 g)), ((nb078AlphaDummy543), (nb078AlphaDummy546 g)),
        ((nb078AlphaDummy541), (nb078AlphaDummy542 g)), ((nb078AlphaDummy537),
        (nb078AlphaDummy539 g)), ((nb078AlphaDummy538), (nb078AlphaDummy540 g)),
        ((nb078AlphaDummy563), (nb078AlphaDummy564 g)), ((nb078AlphaDummy561),
        (nb078AlphaDummy562 g)), ((nb078AlphaDummy530), (nb078AlphaDummy532 g)),
        ((nb078AlphaDummy529), (nb078AlphaDummy531 g)), ((nb078AlphaDummy559),
        (nb078AlphaDummy560 g)), ((nb078AlphaDummy533), (nb078AlphaDummy534 g)),
        ((nb078AlphaDummy526), (nb078AlphaDummy528 g)), ((nb078AlphaDummy525),
        (nb078AlphaDummy527 g)), ((nb078AlphaDummy523), (nb078AlphaDummy524 x g)),
        ((nb078AlphaDummy521), (nb078AlphaDummy522 x g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy551) from (by
          unfold
            nb078AlphaDummy551;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0554)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy552 g) from (by
          unfold
            nb078AlphaDummy552;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0555
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy549)
        from (by
          unfold
            nb078AlphaDummy549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0552)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy550 g) from (by
          unfold
            nb078AlphaDummy550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0553
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy539 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy551)
        from (by
          unfold
            nb078AlphaDummy551;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0558)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy552 g) from (by
          unfold
            nb078AlphaDummy552;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0559
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy549)
        from (by
          unfold
            nb078AlphaDummy549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0556)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy550 g) from (by
          unfold
            nb078AlphaDummy550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0557
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy551) from (by
          unfold
            nb078AlphaDummy551;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0554)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy552 g) from (by
          unfold
            nb078AlphaDummy552;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0555
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy549)
        from (by
          unfold
            nb078AlphaDummy549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0552)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy550 g) from (by
          unfold
            nb078AlphaDummy550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0553
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy539 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy551)
        from (by
          unfold
            nb078AlphaDummy551;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0558)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy552 g) from (by
          unfold
            nb078AlphaDummy552;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0559
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy549)
        from (by
          unfold
            nb078AlphaDummy549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0556)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy550 g) from (by
          unfold
            nb078AlphaDummy550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0557
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy545), (nb078AlphaDummy548 g)), ((nb078AlphaDummy544),
        (nb078AlphaDummy547 g)), ((nb078AlphaDummy543), (nb078AlphaDummy546 g)),
        ((nb078AlphaDummy541), (nb078AlphaDummy542 g)), ((nb078AlphaDummy537),
        (nb078AlphaDummy539 g)), ((nb078AlphaDummy538), (nb078AlphaDummy540 g)),
        ((nb078AlphaDummy563), (nb078AlphaDummy564 g)), ((nb078AlphaDummy561),
        (nb078AlphaDummy562 g)), ((nb078AlphaDummy530), (nb078AlphaDummy532 g)),
        ((nb078AlphaDummy529), (nb078AlphaDummy531 g)), ((nb078AlphaDummy559),
        (nb078AlphaDummy560 g)), ((nb078AlphaDummy533), (nb078AlphaDummy534 g)),
        ((nb078AlphaDummy526), (nb078AlphaDummy528 g)), ((nb078AlphaDummy525),
        (nb078AlphaDummy527 g)), ((nb078AlphaDummy523), (nb078AlphaDummy524 x g)),
        ((nb078AlphaDummy521), (nb078AlphaDummy522 x g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy537))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy539
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy539 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy544) ≠
        (nb078AlphaDummy555) from (by
          unfold
            nb078AlphaDummy555;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0562)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy556 g) from (by
          unfold
            nb078AlphaDummy556;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0563
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy553)
        from (by
          unfold
            nb078AlphaDummy553;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0560)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy554 g) from (by
          unfold
            nb078AlphaDummy554;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0561
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy539 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy555)
        from (by
          unfold
            nb078AlphaDummy555;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0562)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy556 g) from (by
          unfold
            nb078AlphaDummy556;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0563
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy553)
        from (by
          unfold
            nb078AlphaDummy553;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0560)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy554 g) from (by
          unfold
            nb078AlphaDummy554;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0561
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy539 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy557) from (by
          unfold
            nb078AlphaDummy557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0566)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy558 g) from (by
          unfold
            nb078AlphaDummy558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0567
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy553)
        from (by
          unfold
            nb078AlphaDummy553;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0564)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy554 g) from (by
          unfold
            nb078AlphaDummy554;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0565
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy545) ≠
        (nb078AlphaDummy557) from (by
          unfold
            nb078AlphaDummy557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0566)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy558 g) from (by
          unfold
            nb078AlphaDummy558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0567
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy553)
        from (by
          unfold
            nb078AlphaDummy553;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0564)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy554 g) from (by
          unfold
            nb078AlphaDummy554;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0565
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy537) ≠ (nb078AlphaDummy541) from
                                        (by
                                          unfold nb078AlphaDummy541;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0548)
                                                  0)))) (show (nb078AlphaDummy539 g) ≠
        (nb078AlphaDummy542 g) from (by
                                          unfold nb078AlphaDummy542;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0549 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy541), (nb078AlphaDummy542 g)),
                                      ((nb078AlphaDummy537), (nb078AlphaDummy539 g)),
                                      ((nb078AlphaDummy538), (nb078AlphaDummy540 g)),
                                      ((nb078AlphaDummy563), (nb078AlphaDummy564 g)),
                                      ((nb078AlphaDummy561), (nb078AlphaDummy562 g)),
                                      ((nb078AlphaDummy530), (nb078AlphaDummy532 g)),
                                      ((nb078AlphaDummy529), (nb078AlphaDummy531 g)),
                                      ((nb078AlphaDummy559), (nb078AlphaDummy560 g)),
                                      ((nb078AlphaDummy533), (nb078AlphaDummy534 g)),
                                      ((nb078AlphaDummy526), (nb078AlphaDummy528 g)),
                                      ((nb078AlphaDummy525), (nb078AlphaDummy527 g)),
                                      ((nb078AlphaDummy523), (nb078AlphaDummy524 x g)),
                                      ((nb078AlphaDummy521), (nb078AlphaDummy522 x g)),
                                      ((nb078AlphaDummy001), g),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy537) ≠ (nb078AlphaDummy541) from (by
                                        unfold nb078AlphaDummy541;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0548)
                                                0)))) (show (nb078AlphaDummy539 g) ≠
                                        (nb078AlphaDummy542 g) from (by
                                        unfold nb078AlphaDummy542;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0549 g)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy537) ≠ (nb078AlphaDummy541) from
                                        (by
                                          unfold nb078AlphaDummy541;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0548)
                                                  0)))) (show (nb078AlphaDummy539 g) ≠
        (nb078AlphaDummy542 g) from (by
                                          unfold nb078AlphaDummy542;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0549 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy541), (nb078AlphaDummy542 g)),
                                      ((nb078AlphaDummy537), (nb078AlphaDummy539 g)),
                                      ((nb078AlphaDummy538), (nb078AlphaDummy540 g)),
                                      ((nb078AlphaDummy563), (nb078AlphaDummy564 g)),
                                      ((nb078AlphaDummy561), (nb078AlphaDummy562 g)),
                                      ((nb078AlphaDummy530), (nb078AlphaDummy532 g)),
                                      ((nb078AlphaDummy529), (nb078AlphaDummy531 g)),
                                      ((nb078AlphaDummy559), (nb078AlphaDummy560 g)),
                                      ((nb078AlphaDummy533), (nb078AlphaDummy534 g)),
                                      ((nb078AlphaDummy526), (nb078AlphaDummy528 g)),
                                      ((nb078AlphaDummy525), (nb078AlphaDummy527 g)),
                                      ((nb078AlphaDummy523), (nb078AlphaDummy524 x g)),
                                      ((nb078AlphaDummy521), (nb078AlphaDummy522 x g)),
                                      ((nb078AlphaDummy001), g),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
          [((nb078AlphaDummy561), (nb078AlphaDummy562 g)),
            ((nb078AlphaDummy530), (nb078AlphaDummy532 g)),
            ((nb078AlphaDummy529), (nb078AlphaDummy531 g)),
            ((nb078AlphaDummy559), (nb078AlphaDummy560 g)),
            ((nb078AlphaDummy533), (nb078AlphaDummy534 g)),
            ((nb078AlphaDummy526), (nb078AlphaDummy528 g)),
            ((nb078AlphaDummy525), (nb078AlphaDummy527 g)),
            ((nb078AlphaDummy523), (nb078AlphaDummy524 x g)),
            ((nb078AlphaDummy521), (nb078AlphaDummy522 x g)),
            ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
            ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part088`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0060`. -/
@[expose]
noncomputable def nb078SplitAlpha0060 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078AlphaDummy530), (nb078AlphaDummy532 g)),
        ((nb078AlphaDummy529), (nb078AlphaDummy531 g)),
        ((nb078AlphaDummy559), (nb078AlphaDummy560 g)),
        ((nb078AlphaDummy533), (nb078AlphaDummy534 g)),
        ((nb078AlphaDummy526), (nb078AlphaDummy528 g)),
        ((nb078AlphaDummy525), (nb078AlphaDummy527 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy530))
          (Class.cv (nb078AlphaDummy525))) (Wff.neg
          (Wff.classEq (Class.cv (nb078AlphaDummy529))
            (synCun (synCphi (Class.cv (nb078AlphaDummy530))) (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy532 g))
          (Class.cv (nb078AlphaDummy527 g))) (Wff.neg
          (Wff.classEq (Class.cv (nb078AlphaDummy531 g))
            (synCun (synCphi (Class.cv (nb078AlphaDummy532 g))) (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy525) ≠ (nb078AlphaDummy530) from (by
              unfold nb078AlphaDummy530;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0568) 1))))
          (show (nb078AlphaDummy527 g) ≠ (nb078AlphaDummy532 g) from (by
              unfold nb078AlphaDummy532;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0570 g) 1))))
          (TAlphaVar.there (show (nb078AlphaDummy525) ≠ (nb078AlphaDummy529) from (by
                unfold nb078AlphaDummy529;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0568) 0))))
            (show (nb078AlphaDummy527 g) ≠ (nb078AlphaDummy531 g) from (by
                unfold nb078AlphaDummy531;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0570 g) 0))))
            (TAlphaVar.there (show (nb078AlphaDummy525) ≠ (nb078AlphaDummy559) from (by
                  unfold nb078AlphaDummy559;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0572) 0))))
              (show (nb078AlphaDummy527 g) ≠ (nb078AlphaDummy560 g) from (by
                  unfold nb078AlphaDummy560;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0573 g) 0))))
              (TAlphaVar.there (show (nb078AlphaDummy525) ≠ (nb078AlphaDummy533) from (by
                    unfold nb078AlphaDummy533;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0569) 0))))
                (show (nb078AlphaDummy527 g) ≠ (nb078AlphaDummy534 g) from (by
                    unfold nb078AlphaDummy534;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0571 g) 0))))
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb078AlphaDummy001))).fv ∪ ((synCvv)).fv) (by decide))
                  (freshVar_injective (((Class.cv g)).fv ∪ ((synCvv)).fv) (by decide))
                  (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb078AlphaDummy526))).fv ∪
                ((Class.cv (nb078AlphaDummy525))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb078AlphaDummy528 g))).fv ∪
                ((Class.cv (nb078AlphaDummy527 g))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy530) ≠ (nb078AlphaDummy537) from (by
                                        unfold nb078AlphaDummy537;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0546)
                                                0)))) (show (nb078AlphaDummy532 g) ≠
                                        (nb078AlphaDummy539 g) from (by
                                        unfold nb078AlphaDummy539;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0547 g)
                                                0)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy530) ≠ (nb078AlphaDummy538) from
                                        (by
                                          unfold nb078AlphaDummy538;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0546)
                                                  1)))) (show (nb078AlphaDummy532 g) ≠
        (nb078AlphaDummy540 g) from (by
                                          unfold nb078AlphaDummy540;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0547 g) 1))))
                                      (TAlphaVar.there (show (nb078AlphaDummy530) ≠
        (nb078AlphaDummy563) from (by
          unfold nb078AlphaDummy563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0576) 0)))) (show (nb078AlphaDummy532 g) ≠
        (nb078AlphaDummy564 g) from (by
          unfold nb078AlphaDummy564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0577 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy530) ≠ (nb078AlphaDummy561) from (by
          unfold nb078AlphaDummy561;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0574) 0)))) (show (nb078AlphaDummy532 g) ≠
        (nb078AlphaDummy562 g) from (by
          unfold nb078AlphaDummy562;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0575 g) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb078AlphaDummy530))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb078AlphaDummy532 g))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy537) ≠ (nb078AlphaDummy544) from (by
          unfold nb078AlphaDummy544;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0550)
                  1)))) (show (nb078AlphaDummy539 g) ≠ (nb078AlphaDummy547 g) from (by
          unfold nb078AlphaDummy547;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0551
                    g)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy537) ≠ (nb078AlphaDummy543)
        from (by
          unfold nb078AlphaDummy543;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0550)
                  0)))) (show (nb078AlphaDummy539 g) ≠ (nb078AlphaDummy546 g) from (by
          unfold nb078AlphaDummy546;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0551
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy537) ≠ (nb078AlphaDummy541)
        from (by
          unfold
            nb078AlphaDummy541;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0548)
                  0)))) (show (nb078AlphaDummy539 g) ≠ (nb078AlphaDummy542 g) from (by
          unfold
            nb078AlphaDummy542;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0549
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy545), (nb078AlphaDummy548 g)), ((nb078AlphaDummy544),
        (nb078AlphaDummy547 g)), ((nb078AlphaDummy543), (nb078AlphaDummy546 g)),
        ((nb078AlphaDummy541), (nb078AlphaDummy542 g)), ((nb078AlphaDummy537),
        (nb078AlphaDummy539 g)), ((nb078AlphaDummy538), (nb078AlphaDummy540 g)),
        ((nb078AlphaDummy563), (nb078AlphaDummy564 g)), ((nb078AlphaDummy561),
        (nb078AlphaDummy562 g)), ((nb078AlphaDummy530), (nb078AlphaDummy532 g)),
        ((nb078AlphaDummy529), (nb078AlphaDummy531 g)), ((nb078AlphaDummy559),
        (nb078AlphaDummy560 g)), ((nb078AlphaDummy533), (nb078AlphaDummy534 g)),
        ((nb078AlphaDummy526), (nb078AlphaDummy528 g)), ((nb078AlphaDummy525),
        (nb078AlphaDummy527 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy551) from (by
          unfold
            nb078AlphaDummy551;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0554)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy552 g) from (by
          unfold
            nb078AlphaDummy552;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0555
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy549)
        from (by
          unfold
            nb078AlphaDummy549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0552)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy550 g) from (by
          unfold
            nb078AlphaDummy550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0553
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy539 g))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy545) ≠
        (nb078AlphaDummy551) from (by
          unfold
            nb078AlphaDummy551;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0558)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy552 g) from (by
          unfold
            nb078AlphaDummy552;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0559
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy549)
        from (by
          unfold
            nb078AlphaDummy549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0556)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy550 g) from (by
          unfold
            nb078AlphaDummy550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0557
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy551) from (by
          unfold
            nb078AlphaDummy551;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0554)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy552 g) from (by
          unfold
            nb078AlphaDummy552;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0555
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy549)
        from (by
          unfold
            nb078AlphaDummy549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0552)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy550 g) from (by
          unfold
            nb078AlphaDummy550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0553
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy539 g))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy545) ≠
        (nb078AlphaDummy551) from (by
          unfold
            nb078AlphaDummy551;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0558)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy552 g) from (by
          unfold
            nb078AlphaDummy552;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0559
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy549)
        from (by
          unfold
            nb078AlphaDummy549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0556)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy550 g) from (by
          unfold
            nb078AlphaDummy550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0557
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy545), (nb078AlphaDummy548 g)), ((nb078AlphaDummy544),
        (nb078AlphaDummy547 g)), ((nb078AlphaDummy543), (nb078AlphaDummy546 g)),
        ((nb078AlphaDummy541), (nb078AlphaDummy542 g)), ((nb078AlphaDummy537),
        (nb078AlphaDummy539 g)), ((nb078AlphaDummy538), (nb078AlphaDummy540 g)),
        ((nb078AlphaDummy563), (nb078AlphaDummy564 g)), ((nb078AlphaDummy561),
        (nb078AlphaDummy562 g)), ((nb078AlphaDummy530), (nb078AlphaDummy532 g)),
        ((nb078AlphaDummy529), (nb078AlphaDummy531 g)), ((nb078AlphaDummy559),
        (nb078AlphaDummy560 g)), ((nb078AlphaDummy533), (nb078AlphaDummy534 g)),
        ((nb078AlphaDummy526), (nb078AlphaDummy528 g)), ((nb078AlphaDummy525),
        (nb078AlphaDummy527 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy539 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy537))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy539
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy555) from (by
          unfold
            nb078AlphaDummy555;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0562)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy556 g) from (by
          unfold
            nb078AlphaDummy556;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0563
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy553)
        from (by
          unfold
            nb078AlphaDummy553;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0560)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy554 g) from (by
          unfold
            nb078AlphaDummy554;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0561
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy539 g))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy544) ≠
        (nb078AlphaDummy555) from (by
          unfold
            nb078AlphaDummy555;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0562)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy556 g) from (by
          unfold
            nb078AlphaDummy556;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0563
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy553)
        from (by
          unfold
            nb078AlphaDummy553;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0560)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy554 g) from (by
          unfold
            nb078AlphaDummy554;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0561
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy539 g))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy557) from (by
          unfold
            nb078AlphaDummy557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0566)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy558 g) from (by
          unfold
            nb078AlphaDummy558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0567
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy553)
        from (by
          unfold
            nb078AlphaDummy553;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0564)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy554 g) from (by
          unfold
            nb078AlphaDummy554;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0565
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy545) ≠
        (nb078AlphaDummy557) from (by
          unfold
            nb078AlphaDummy557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0566)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy558 g) from (by
          unfold
            nb078AlphaDummy558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0567
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy553)
        from (by
          unfold
            nb078AlphaDummy553;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0564)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy554 g) from (by
          unfold
            nb078AlphaDummy554;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0565
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy537) ≠ (nb078AlphaDummy541)
        from (by
          unfold nb078AlphaDummy541;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0548) 0)))) (show (nb078AlphaDummy539 g) ≠
        (nb078AlphaDummy542 g) from (by
          unfold nb078AlphaDummy542;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0549 g) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb078AlphaDummy541), (nb078AlphaDummy542 g)),
        ((nb078AlphaDummy537), (nb078AlphaDummy539 g)), ((nb078AlphaDummy538),
        (nb078AlphaDummy540 g)), ((nb078AlphaDummy563), (nb078AlphaDummy564 g)),
        ((nb078AlphaDummy561), (nb078AlphaDummy562 g)), ((nb078AlphaDummy530),
        (nb078AlphaDummy532 g)), ((nb078AlphaDummy529), (nb078AlphaDummy531 g)),
        ((nb078AlphaDummy559), (nb078AlphaDummy560 g)), ((nb078AlphaDummy533),
        (nb078AlphaDummy534 g)), ((nb078AlphaDummy526), (nb078AlphaDummy528 g)),
        ((nb078AlphaDummy525), (nb078AlphaDummy527 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy537) ≠ (nb078AlphaDummy541) from (by
          unfold nb078AlphaDummy541;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0548) 0)))) (show (nb078AlphaDummy539 g) ≠
        (nb078AlphaDummy542 g) from (by
          unfold nb078AlphaDummy542;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0549 g) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb078AlphaDummy537) ≠ (nb078AlphaDummy541) from (by
          unfold nb078AlphaDummy541;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0548) 0)))) (show (nb078AlphaDummy539 g) ≠
        (nb078AlphaDummy542 g) from (by
          unfold nb078AlphaDummy542;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0549 g) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb078AlphaDummy541), (nb078AlphaDummy542 g)),
        ((nb078AlphaDummy537), (nb078AlphaDummy539 g)), ((nb078AlphaDummy538),
        (nb078AlphaDummy540 g)), ((nb078AlphaDummy563), (nb078AlphaDummy564 g)),
        ((nb078AlphaDummy561), (nb078AlphaDummy562 g)), ((nb078AlphaDummy530),
        (nb078AlphaDummy532 g)), ((nb078AlphaDummy529), (nb078AlphaDummy531 g)),
        ((nb078AlphaDummy559), (nb078AlphaDummy560 g)), ((nb078AlphaDummy533),
        (nb078AlphaDummy534 g)), ((nb078AlphaDummy526), (nb078AlphaDummy528 g)),
        ((nb078AlphaDummy525), (nb078AlphaDummy527 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)] (synCnnc)
        (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy530) ≠ (nb078AlphaDummy537) from (by
                                        unfold nb078AlphaDummy537;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0546)
                                                0)))) (show (nb078AlphaDummy532 g) ≠
                                        (nb078AlphaDummy539 g) from (by
                                        unfold nb078AlphaDummy539;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0547 g)
                                                0)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy530) ≠ (nb078AlphaDummy538) from
                                        (by
                                          unfold nb078AlphaDummy538;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0546)
                                                  1)))) (show (nb078AlphaDummy532 g) ≠
        (nb078AlphaDummy540 g) from (by
                                          unfold nb078AlphaDummy540;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0547 g) 1))))
                                      (TAlphaVar.there (show (nb078AlphaDummy530) ≠
        (nb078AlphaDummy563) from (by
          unfold nb078AlphaDummy563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0576) 0)))) (show (nb078AlphaDummy532 g) ≠
        (nb078AlphaDummy564 g) from (by
          unfold nb078AlphaDummy564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0577 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy530) ≠ (nb078AlphaDummy561) from (by
          unfold nb078AlphaDummy561;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0574) 0)))) (show (nb078AlphaDummy532 g) ≠
        (nb078AlphaDummy562 g) from (by
          unfold nb078AlphaDummy562;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0575 g) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb078AlphaDummy530))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb078AlphaDummy532 g))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy537) ≠ (nb078AlphaDummy544) from (by
          unfold nb078AlphaDummy544;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0550)
                  1)))) (show (nb078AlphaDummy539 g) ≠ (nb078AlphaDummy547 g) from (by
          unfold nb078AlphaDummy547;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0551
                    g)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy537) ≠ (nb078AlphaDummy543)
        from (by
          unfold nb078AlphaDummy543;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0550)
                  0)))) (show (nb078AlphaDummy539 g) ≠ (nb078AlphaDummy546 g) from (by
          unfold nb078AlphaDummy546;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0551
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy537) ≠ (nb078AlphaDummy541)
        from (by
          unfold
            nb078AlphaDummy541;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0548)
                  0)))) (show (nb078AlphaDummy539 g) ≠ (nb078AlphaDummy542 g) from (by
          unfold
            nb078AlphaDummy542;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0549
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy545), (nb078AlphaDummy548 g)), ((nb078AlphaDummy544),
        (nb078AlphaDummy547 g)), ((nb078AlphaDummy543), (nb078AlphaDummy546 g)),
        ((nb078AlphaDummy541), (nb078AlphaDummy542 g)), ((nb078AlphaDummy537),
        (nb078AlphaDummy539 g)), ((nb078AlphaDummy538), (nb078AlphaDummy540 g)),
        ((nb078AlphaDummy563), (nb078AlphaDummy564 g)), ((nb078AlphaDummy561),
        (nb078AlphaDummy562 g)), ((nb078AlphaDummy530), (nb078AlphaDummy532 g)),
        ((nb078AlphaDummy529), (nb078AlphaDummy531 g)), ((nb078AlphaDummy559),
        (nb078AlphaDummy560 g)), ((nb078AlphaDummy533), (nb078AlphaDummy534 g)),
        ((nb078AlphaDummy526), (nb078AlphaDummy528 g)), ((nb078AlphaDummy525),
        (nb078AlphaDummy527 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy551) from (by
          unfold
            nb078AlphaDummy551;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0554)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy552 g) from (by
          unfold
            nb078AlphaDummy552;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0555
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy549)
        from (by
          unfold
            nb078AlphaDummy549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0552)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy550 g) from (by
          unfold
            nb078AlphaDummy550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0553
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy539 g))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy545) ≠
        (nb078AlphaDummy551) from (by
          unfold
            nb078AlphaDummy551;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0558)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy552 g) from (by
          unfold
            nb078AlphaDummy552;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0559
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy549)
        from (by
          unfold
            nb078AlphaDummy549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0556)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy550 g) from (by
          unfold
            nb078AlphaDummy550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0557
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy551) from (by
          unfold
            nb078AlphaDummy551;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0554)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy552 g) from (by
          unfold
            nb078AlphaDummy552;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0555
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy549)
        from (by
          unfold
            nb078AlphaDummy549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0552)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy550 g) from (by
          unfold
            nb078AlphaDummy550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0553
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy539 g))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy545) ≠
        (nb078AlphaDummy551) from (by
          unfold
            nb078AlphaDummy551;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0558)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy552 g) from (by
          unfold
            nb078AlphaDummy552;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0559
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy549)
        from (by
          unfold
            nb078AlphaDummy549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0556)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy550 g) from (by
          unfold
            nb078AlphaDummy550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0557
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy545), (nb078AlphaDummy548 g)), ((nb078AlphaDummy544),
        (nb078AlphaDummy547 g)), ((nb078AlphaDummy543), (nb078AlphaDummy546 g)),
        ((nb078AlphaDummy541), (nb078AlphaDummy542 g)), ((nb078AlphaDummy537),
        (nb078AlphaDummy539 g)), ((nb078AlphaDummy538), (nb078AlphaDummy540 g)),
        ((nb078AlphaDummy563), (nb078AlphaDummy564 g)), ((nb078AlphaDummy561),
        (nb078AlphaDummy562 g)), ((nb078AlphaDummy530), (nb078AlphaDummy532 g)),
        ((nb078AlphaDummy529), (nb078AlphaDummy531 g)), ((nb078AlphaDummy559),
        (nb078AlphaDummy560 g)), ((nb078AlphaDummy533), (nb078AlphaDummy534 g)),
        ((nb078AlphaDummy526), (nb078AlphaDummy528 g)), ((nb078AlphaDummy525),
        (nb078AlphaDummy527 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy539 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy537))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy539
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy555) from (by
          unfold
            nb078AlphaDummy555;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0562)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy556 g) from (by
          unfold
            nb078AlphaDummy556;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0563
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy553)
        from (by
          unfold
            nb078AlphaDummy553;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0560)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy554 g) from (by
          unfold
            nb078AlphaDummy554;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0561
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy539 g))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy544) ≠
        (nb078AlphaDummy555) from (by
          unfold
            nb078AlphaDummy555;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0562)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy556 g) from (by
          unfold
            nb078AlphaDummy556;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0563
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy553)
        from (by
          unfold
            nb078AlphaDummy553;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0560)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy554 g) from (by
          unfold
            nb078AlphaDummy554;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0561
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy539 g))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy557) from (by
          unfold
            nb078AlphaDummy557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0566)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy558 g) from (by
          unfold
            nb078AlphaDummy558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0567
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy553)
        from (by
          unfold
            nb078AlphaDummy553;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0564)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy554 g) from (by
          unfold
            nb078AlphaDummy554;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0565
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy545) ≠
        (nb078AlphaDummy557) from (by
          unfold
            nb078AlphaDummy557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0566)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy558 g) from (by
          unfold
            nb078AlphaDummy558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0567
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy553)
        from (by
          unfold
            nb078AlphaDummy553;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0564)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy554 g) from (by
          unfold
            nb078AlphaDummy554;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0565
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy537) ≠ (nb078AlphaDummy541)
        from (by
          unfold nb078AlphaDummy541;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0548) 0)))) (show (nb078AlphaDummy539 g) ≠
        (nb078AlphaDummy542 g) from (by
          unfold nb078AlphaDummy542;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0549 g) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb078AlphaDummy541), (nb078AlphaDummy542 g)),
        ((nb078AlphaDummy537), (nb078AlphaDummy539 g)), ((nb078AlphaDummy538),
        (nb078AlphaDummy540 g)), ((nb078AlphaDummy563), (nb078AlphaDummy564 g)),
        ((nb078AlphaDummy561), (nb078AlphaDummy562 g)), ((nb078AlphaDummy530),
        (nb078AlphaDummy532 g)), ((nb078AlphaDummy529), (nb078AlphaDummy531 g)),
        ((nb078AlphaDummy559), (nb078AlphaDummy560 g)), ((nb078AlphaDummy533),
        (nb078AlphaDummy534 g)), ((nb078AlphaDummy526), (nb078AlphaDummy528 g)),
        ((nb078AlphaDummy525), (nb078AlphaDummy527 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy537) ≠ (nb078AlphaDummy541) from (by
          unfold nb078AlphaDummy541;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0548) 0)))) (show (nb078AlphaDummy539 g) ≠
        (nb078AlphaDummy542 g) from (by
          unfold nb078AlphaDummy542;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0549 g) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb078AlphaDummy537) ≠ (nb078AlphaDummy541) from (by
          unfold nb078AlphaDummy541;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0548) 0)))) (show (nb078AlphaDummy539 g) ≠
        (nb078AlphaDummy542 g) from (by
          unfold nb078AlphaDummy542;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0549 g) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb078AlphaDummy541), (nb078AlphaDummy542 g)),
        ((nb078AlphaDummy537), (nb078AlphaDummy539 g)), ((nb078AlphaDummy538),
        (nb078AlphaDummy540 g)), ((nb078AlphaDummy563), (nb078AlphaDummy564 g)),
        ((nb078AlphaDummy561), (nb078AlphaDummy562 g)), ((nb078AlphaDummy530),
        (nb078AlphaDummy532 g)), ((nb078AlphaDummy529), (nb078AlphaDummy531 g)),
        ((nb078AlphaDummy559), (nb078AlphaDummy560 g)), ((nb078AlphaDummy533),
        (nb078AlphaDummy534 g)), ((nb078AlphaDummy526), (nb078AlphaDummy528 g)),
        ((nb078AlphaDummy525), (nb078AlphaDummy527 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)] (synCnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb078AlphaDummy561), (nb078AlphaDummy562 g)),
                    ((nb078AlphaDummy530), (nb078AlphaDummy532 g)),
                    ((nb078AlphaDummy529), (nb078AlphaDummy531 g)),
                    ((nb078AlphaDummy559), (nb078AlphaDummy560 g)),
                    ((nb078AlphaDummy533), (nb078AlphaDummy534 g)),
                    ((nb078AlphaDummy526), (nb078AlphaDummy528 g)),
                    ((nb078AlphaDummy525), (nb078AlphaDummy527 g)),
                    ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                    ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0061`. -/
@[expose]
noncomputable def nb078SplitAlpha0061 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078AlphaDummy533), (nb078AlphaDummy534 g)),
        ((nb078AlphaDummy526), (nb078AlphaDummy528 g)),
        ((nb078AlphaDummy525), (nb078AlphaDummy527 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy533)) (synCcompl
            (Class.cab (nb078AlphaDummy529)
              (synWrex (nb078AlphaDummy530) (Class.cv (nb078AlphaDummy526))
                (Wff.classEq (Class.cv (nb078AlphaDummy529))
                  (synCphi (Class.cv (nb078AlphaDummy530)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy533)) (synCcompl
              (Class.cab (nb078AlphaDummy529)
                (synWrex (nb078AlphaDummy530) (Class.cv (nb078AlphaDummy525))
                  (Wff.classEq (Class.cv (nb078AlphaDummy529))
                    (synCun (synCphi (Class.cv (nb078AlphaDummy530)))
                      (synCsn (synC0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy534 g)) (synCcompl
            (Class.cab (nb078AlphaDummy531 g)
              (synWrex (nb078AlphaDummy532 g) (Class.cv (nb078AlphaDummy528 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy531 g))
                  (synCphi (Class.cv (nb078AlphaDummy532 g)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy534 g)) (synCcompl
              (Class.cab (nb078AlphaDummy531 g)
                (synWrex (nb078AlphaDummy532 g) (Class.cv (nb078AlphaDummy527 g))
                  (Wff.classEq (Class.cv (nb078AlphaDummy531 g))
                    (synCun (synCphi (Class.cv (nb078AlphaDummy532 g)))
                      (synCsn (synC0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy526) ≠ (nb078AlphaDummy530) from (by
                              unfold nb078AlphaDummy530;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0540) 1))))
                          (show (nb078AlphaDummy528 g) ≠ (nb078AlphaDummy532 g) from (by
                              unfold nb078AlphaDummy532;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0542 g) 1))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy526) ≠ (nb078AlphaDummy529) from (by
                                unfold nb078AlphaDummy529;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0540) 0))))
                            (show (nb078AlphaDummy528 g) ≠ (nb078AlphaDummy531 g) from (by
                                unfold nb078AlphaDummy531;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0542 g) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy526) ≠ (nb078AlphaDummy535) from (by
                                  unfold nb078AlphaDummy535;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0544) 0))))
                              (show (nb078AlphaDummy528 g) ≠ (nb078AlphaDummy536 g) from
                                (by
                                  unfold nb078AlphaDummy536;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0545 g) 0))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy526) ≠ (nb078AlphaDummy533) from (by
                                    unfold nb078AlphaDummy533;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0541) 0)))) (show
                                  (nb078AlphaDummy528 g) ≠ (nb078AlphaDummy534 g) from (by
                                    unfold nb078AlphaDummy534;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0543 g)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb078AlphaDummy526))).fv ∪
                              ((Class.cv (nb078AlphaDummy525))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy528 g))).fv ∪
                              ((Class.cv (nb078AlphaDummy527 g))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy530) ≠ (nb078AlphaDummy537) from
                                    (by
                                      unfold nb078AlphaDummy537;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0546)
                                              0)))) (show
                                    (nb078AlphaDummy532 g) ≠ (nb078AlphaDummy539 g) from
                                    (by
                                      unfold nb078AlphaDummy539;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0547 g)
                                              0)))) (TAlphaVar.there (show
                                      (nb078AlphaDummy530) ≠ (nb078AlphaDummy538) from (by
                                        unfold nb078AlphaDummy538;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0546)
                                                1)))) (show (nb078AlphaDummy532 g) ≠
                                        (nb078AlphaDummy540 g) from (by
                                        unfold nb078AlphaDummy540;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0547 g)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb078AlphaDummy530))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb078AlphaDummy532 g))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy537) ≠ (nb078AlphaDummy544) from (by
          unfold nb078AlphaDummy544;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0550)
                  1)))) (show (nb078AlphaDummy539 g) ≠ (nb078AlphaDummy547 g) from (by
          unfold nb078AlphaDummy547;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0551 g)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy537) ≠ (nb078AlphaDummy543)
        from (by
          unfold nb078AlphaDummy543;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0550)
                  0)))) (show (nb078AlphaDummy539 g) ≠ (nb078AlphaDummy546 g) from (by
          unfold nb078AlphaDummy546;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0551
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy537) ≠ (nb078AlphaDummy541)
        from (by
          unfold nb078AlphaDummy541;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0548)
                  0)))) (show (nb078AlphaDummy539 g) ≠ (nb078AlphaDummy542 g) from (by
          unfold nb078AlphaDummy542;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0549
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy545), (nb078AlphaDummy548 g)), ((nb078AlphaDummy544),
        (nb078AlphaDummy547 g)), ((nb078AlphaDummy543), (nb078AlphaDummy546 g)),
        ((nb078AlphaDummy541), (nb078AlphaDummy542 g)), ((nb078AlphaDummy537),
        (nb078AlphaDummy539 g)), ((nb078AlphaDummy538), (nb078AlphaDummy540 g)),
        ((nb078AlphaDummy530), (nb078AlphaDummy532 g)), ((nb078AlphaDummy529),
        (nb078AlphaDummy531 g)), ((nb078AlphaDummy535), (nb078AlphaDummy536 g)),
        ((nb078AlphaDummy533), (nb078AlphaDummy534 g)), ((nb078AlphaDummy526),
        (nb078AlphaDummy528 g)), ((nb078AlphaDummy525), (nb078AlphaDummy527 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy551) from (by
          unfold
            nb078AlphaDummy551;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0554)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy552 g) from (by
          unfold
            nb078AlphaDummy552;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0555
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy549)
        from (by
          unfold
            nb078AlphaDummy549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0552)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy550 g) from (by
          unfold
            nb078AlphaDummy550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0553
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy539 g))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy545) ≠
        (nb078AlphaDummy551) from (by
          unfold
            nb078AlphaDummy551;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0558)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy552 g) from (by
          unfold
            nb078AlphaDummy552;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0559
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy549)
        from (by
          unfold
            nb078AlphaDummy549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0556)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy550 g) from (by
          unfold
            nb078AlphaDummy550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0557
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy551) from (by
          unfold
            nb078AlphaDummy551;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0554)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy552 g) from (by
          unfold
            nb078AlphaDummy552;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0555
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy549)
        from (by
          unfold
            nb078AlphaDummy549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0552)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy550 g) from (by
          unfold
            nb078AlphaDummy550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0553
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy539 g))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy545) ≠
        (nb078AlphaDummy551) from (by
          unfold
            nb078AlphaDummy551;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0558)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy552 g) from (by
          unfold
            nb078AlphaDummy552;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0559
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy549)
        from (by
          unfold
            nb078AlphaDummy549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0556)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy550 g) from (by
          unfold
            nb078AlphaDummy550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0557
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy545), (nb078AlphaDummy548 g)), ((nb078AlphaDummy544),
        (nb078AlphaDummy547 g)), ((nb078AlphaDummy543), (nb078AlphaDummy546 g)),
        ((nb078AlphaDummy541), (nb078AlphaDummy542 g)), ((nb078AlphaDummy537),
        (nb078AlphaDummy539 g)), ((nb078AlphaDummy538), (nb078AlphaDummy540 g)),
        ((nb078AlphaDummy530), (nb078AlphaDummy532 g)), ((nb078AlphaDummy529),
        (nb078AlphaDummy531 g)), ((nb078AlphaDummy535), (nb078AlphaDummy536 g)),
        ((nb078AlphaDummy533), (nb078AlphaDummy534 g)), ((nb078AlphaDummy526),
        (nb078AlphaDummy528 g)), ((nb078AlphaDummy525), (nb078AlphaDummy527 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy539 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy537))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy539
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy555) from (by
          unfold
            nb078AlphaDummy555;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0562)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy556 g) from (by
          unfold
            nb078AlphaDummy556;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0563
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy553)
        from (by
          unfold
            nb078AlphaDummy553;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0560)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy554 g) from (by
          unfold
            nb078AlphaDummy554;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0561
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy539 g))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy544) ≠
        (nb078AlphaDummy555) from (by
          unfold
            nb078AlphaDummy555;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0562)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy556 g) from (by
          unfold
            nb078AlphaDummy556;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0563
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy553)
        from (by
          unfold
            nb078AlphaDummy553;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0560)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy554 g) from (by
          unfold
            nb078AlphaDummy554;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0561
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy539 g))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy557) from (by
          unfold
            nb078AlphaDummy557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0566)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy558 g) from (by
          unfold
            nb078AlphaDummy558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0567
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy553)
        from (by
          unfold
            nb078AlphaDummy553;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0564)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy554 g) from (by
          unfold
            nb078AlphaDummy554;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0565
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy545) ≠
        (nb078AlphaDummy557) from (by
          unfold
            nb078AlphaDummy557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0566)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy558 g) from (by
          unfold
            nb078AlphaDummy558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0567
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy553)
        from (by
          unfold
            nb078AlphaDummy553;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0564)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy554 g) from (by
          unfold
            nb078AlphaDummy554;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0565
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy537) ≠ (nb078AlphaDummy541) from (by
          unfold nb078AlphaDummy541;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0548) 0)))) (show (nb078AlphaDummy539 g) ≠
        (nb078AlphaDummy542 g) from (by
          unfold nb078AlphaDummy542;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0549 g) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed [((nb078AlphaDummy541),
        (nb078AlphaDummy542 g)), ((nb078AlphaDummy537), (nb078AlphaDummy539 g)),
        ((nb078AlphaDummy538), (nb078AlphaDummy540 g)), ((nb078AlphaDummy530),
        (nb078AlphaDummy532 g)), ((nb078AlphaDummy529), (nb078AlphaDummy531 g)),
        ((nb078AlphaDummy535), (nb078AlphaDummy536 g)), ((nb078AlphaDummy533),
        (nb078AlphaDummy534 g)), ((nb078AlphaDummy526), (nb078AlphaDummy528 g)),
        ((nb078AlphaDummy525), (nb078AlphaDummy527 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078AlphaDummy537) ≠
        (nb078AlphaDummy541) from (by
          unfold nb078AlphaDummy541;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0548) 0)))) (show (nb078AlphaDummy539 g) ≠
        (nb078AlphaDummy542 g) from (by
          unfold nb078AlphaDummy542;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0549 g) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy537) ≠ (nb078AlphaDummy541) from (by
          unfold nb078AlphaDummy541;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0548) 0)))) (show (nb078AlphaDummy539 g) ≠
        (nb078AlphaDummy542 g) from (by
          unfold nb078AlphaDummy542;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0549 g) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed [((nb078AlphaDummy541),
        (nb078AlphaDummy542 g)), ((nb078AlphaDummy537), (nb078AlphaDummy539 g)),
        ((nb078AlphaDummy538), (nb078AlphaDummy540 g)), ((nb078AlphaDummy530),
        (nb078AlphaDummy532 g)), ((nb078AlphaDummy529), (nb078AlphaDummy531 g)),
        ((nb078AlphaDummy535), (nb078AlphaDummy536 g)), ((nb078AlphaDummy533),
        (nb078AlphaDummy534 g)), ((nb078AlphaDummy526), (nb078AlphaDummy528 g)),
        ((nb078AlphaDummy525), (nb078AlphaDummy527 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)] (synCnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy526) ≠ (nb078AlphaDummy530) from (by
                              unfold nb078AlphaDummy530;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0540) 1))))
                          (show (nb078AlphaDummy528 g) ≠ (nb078AlphaDummy532 g) from (by
                              unfold nb078AlphaDummy532;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0542 g) 1))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy526) ≠ (nb078AlphaDummy529) from (by
                                unfold nb078AlphaDummy529;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0540) 0))))
                            (show (nb078AlphaDummy528 g) ≠ (nb078AlphaDummy531 g) from (by
                                unfold nb078AlphaDummy531;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0542 g) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy526) ≠ (nb078AlphaDummy535) from (by
                                  unfold nb078AlphaDummy535;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0544) 0))))
                              (show (nb078AlphaDummy528 g) ≠ (nb078AlphaDummy536 g) from
                                (by
                                  unfold nb078AlphaDummy536;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0545 g) 0))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy526) ≠ (nb078AlphaDummy533) from (by
                                    unfold nb078AlphaDummy533;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0541) 0)))) (show
                                  (nb078AlphaDummy528 g) ≠ (nb078AlphaDummy534 g) from (by
                                    unfold nb078AlphaDummy534;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0543 g)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb078AlphaDummy526))).fv ∪
                              ((Class.cv (nb078AlphaDummy525))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy528 g))).fv ∪
                              ((Class.cv (nb078AlphaDummy527 g))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy530) ≠ (nb078AlphaDummy537) from
                                    (by
                                      unfold nb078AlphaDummy537;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0546)
                                              0)))) (show
                                    (nb078AlphaDummy532 g) ≠ (nb078AlphaDummy539 g) from
                                    (by
                                      unfold nb078AlphaDummy539;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0547 g)
                                              0)))) (TAlphaVar.there (show
                                      (nb078AlphaDummy530) ≠ (nb078AlphaDummy538) from (by
                                        unfold nb078AlphaDummy538;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0546)
                                                1)))) (show (nb078AlphaDummy532 g) ≠
                                        (nb078AlphaDummy540 g) from (by
                                        unfold nb078AlphaDummy540;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0547 g)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb078AlphaDummy530))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb078AlphaDummy532 g))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy537) ≠ (nb078AlphaDummy544) from (by
          unfold nb078AlphaDummy544;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0550)
                  1)))) (show (nb078AlphaDummy539 g) ≠ (nb078AlphaDummy547 g) from (by
          unfold nb078AlphaDummy547;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0551 g)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy537) ≠ (nb078AlphaDummy543)
        from (by
          unfold nb078AlphaDummy543;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0550)
                  0)))) (show (nb078AlphaDummy539 g) ≠ (nb078AlphaDummy546 g) from (by
          unfold nb078AlphaDummy546;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0551
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy537) ≠ (nb078AlphaDummy541)
        from (by
          unfold nb078AlphaDummy541;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0548)
                  0)))) (show (nb078AlphaDummy539 g) ≠ (nb078AlphaDummy542 g) from (by
          unfold nb078AlphaDummy542;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0549
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy545), (nb078AlphaDummy548 g)), ((nb078AlphaDummy544),
        (nb078AlphaDummy547 g)), ((nb078AlphaDummy543), (nb078AlphaDummy546 g)),
        ((nb078AlphaDummy541), (nb078AlphaDummy542 g)), ((nb078AlphaDummy537),
        (nb078AlphaDummy539 g)), ((nb078AlphaDummy538), (nb078AlphaDummy540 g)),
        ((nb078AlphaDummy530), (nb078AlphaDummy532 g)), ((nb078AlphaDummy529),
        (nb078AlphaDummy531 g)), ((nb078AlphaDummy535), (nb078AlphaDummy536 g)),
        ((nb078AlphaDummy533), (nb078AlphaDummy534 g)), ((nb078AlphaDummy526),
        (nb078AlphaDummy528 g)), ((nb078AlphaDummy525), (nb078AlphaDummy527 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy551) from (by
          unfold
            nb078AlphaDummy551;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0554)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy552 g) from (by
          unfold
            nb078AlphaDummy552;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0555
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy549)
        from (by
          unfold
            nb078AlphaDummy549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0552)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy550 g) from (by
          unfold
            nb078AlphaDummy550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0553
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy539 g))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy545) ≠
        (nb078AlphaDummy551) from (by
          unfold
            nb078AlphaDummy551;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0558)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy552 g) from (by
          unfold
            nb078AlphaDummy552;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0559
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy549)
        from (by
          unfold
            nb078AlphaDummy549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0556)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy550 g) from (by
          unfold
            nb078AlphaDummy550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0557
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy551) from (by
          unfold
            nb078AlphaDummy551;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0554)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy552 g) from (by
          unfold
            nb078AlphaDummy552;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0555
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy549)
        from (by
          unfold
            nb078AlphaDummy549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0552)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy550 g) from (by
          unfold
            nb078AlphaDummy550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0553
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy539 g))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy545) ≠
        (nb078AlphaDummy551) from (by
          unfold
            nb078AlphaDummy551;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0558)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy552 g) from (by
          unfold
            nb078AlphaDummy552;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0559
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy549)
        from (by
          unfold
            nb078AlphaDummy549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0556)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy550 g) from (by
          unfold
            nb078AlphaDummy550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0557
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy545), (nb078AlphaDummy548 g)), ((nb078AlphaDummy544),
        (nb078AlphaDummy547 g)), ((nb078AlphaDummy543), (nb078AlphaDummy546 g)),
        ((nb078AlphaDummy541), (nb078AlphaDummy542 g)), ((nb078AlphaDummy537),
        (nb078AlphaDummy539 g)), ((nb078AlphaDummy538), (nb078AlphaDummy540 g)),
        ((nb078AlphaDummy530), (nb078AlphaDummy532 g)), ((nb078AlphaDummy529),
        (nb078AlphaDummy531 g)), ((nb078AlphaDummy535), (nb078AlphaDummy536 g)),
        ((nb078AlphaDummy533), (nb078AlphaDummy534 g)), ((nb078AlphaDummy526),
        (nb078AlphaDummy528 g)), ((nb078AlphaDummy525), (nb078AlphaDummy527 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy539 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy537))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy539
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy555) from (by
          unfold
            nb078AlphaDummy555;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0562)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy556 g) from (by
          unfold
            nb078AlphaDummy556;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0563
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy553)
        from (by
          unfold
            nb078AlphaDummy553;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0560)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy554 g) from (by
          unfold
            nb078AlphaDummy554;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0561
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy539 g))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy544) ≠
        (nb078AlphaDummy555) from (by
          unfold
            nb078AlphaDummy555;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0562)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy556 g) from (by
          unfold
            nb078AlphaDummy556;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0563
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy544) ≠ (nb078AlphaDummy553)
        from (by
          unfold
            nb078AlphaDummy553;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0560)
                  0)))) (show (nb078AlphaDummy547 g) ≠ (nb078AlphaDummy554 g) from (by
          unfold
            nb078AlphaDummy554;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0561
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy537))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy539 g))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy557) from (by
          unfold
            nb078AlphaDummy557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0566)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy558 g) from (by
          unfold
            nb078AlphaDummy558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0567
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy553)
        from (by
          unfold
            nb078AlphaDummy553;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0564)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy554 g) from (by
          unfold
            nb078AlphaDummy554;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0565
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy545) ≠
        (nb078AlphaDummy557) from (by
          unfold
            nb078AlphaDummy557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0566)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy558 g) from (by
          unfold
            nb078AlphaDummy558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0567
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy545) ≠ (nb078AlphaDummy553)
        from (by
          unfold
            nb078AlphaDummy553;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0564)
                  0)))) (show (nb078AlphaDummy548 g) ≠ (nb078AlphaDummy554 g) from (by
          unfold
            nb078AlphaDummy554;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0565
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy537) ≠ (nb078AlphaDummy541) from (by
          unfold nb078AlphaDummy541;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0548) 0)))) (show (nb078AlphaDummy539 g) ≠
        (nb078AlphaDummy542 g) from (by
          unfold nb078AlphaDummy542;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0549 g) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed [((nb078AlphaDummy541),
        (nb078AlphaDummy542 g)), ((nb078AlphaDummy537), (nb078AlphaDummy539 g)),
        ((nb078AlphaDummy538), (nb078AlphaDummy540 g)), ((nb078AlphaDummy530),
        (nb078AlphaDummy532 g)), ((nb078AlphaDummy529), (nb078AlphaDummy531 g)),
        ((nb078AlphaDummy535), (nb078AlphaDummy536 g)), ((nb078AlphaDummy533),
        (nb078AlphaDummy534 g)), ((nb078AlphaDummy526), (nb078AlphaDummy528 g)),
        ((nb078AlphaDummy525), (nb078AlphaDummy527 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078AlphaDummy537) ≠
        (nb078AlphaDummy541) from (by
          unfold nb078AlphaDummy541;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0548) 0)))) (show (nb078AlphaDummy539 g) ≠
        (nb078AlphaDummy542 g) from (by
          unfold nb078AlphaDummy542;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0549 g) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy537) ≠ (nb078AlphaDummy541) from (by
          unfold nb078AlphaDummy541;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0548) 0)))) (show (nb078AlphaDummy539 g) ≠
        (nb078AlphaDummy542 g) from (by
          unfold nb078AlphaDummy542;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0549 g) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed [((nb078AlphaDummy541),
        (nb078AlphaDummy542 g)), ((nb078AlphaDummy537), (nb078AlphaDummy539 g)),
        ((nb078AlphaDummy538), (nb078AlphaDummy540 g)), ((nb078AlphaDummy530),
        (nb078AlphaDummy532 g)), ((nb078AlphaDummy529), (nb078AlphaDummy531 g)),
        ((nb078AlphaDummy535), (nb078AlphaDummy536 g)), ((nb078AlphaDummy533),
        (nb078AlphaDummy534 g)), ((nb078AlphaDummy526), (nb078AlphaDummy528 g)),
        ((nb078AlphaDummy525), (nb078AlphaDummy527 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)] (synCnnc)
        (by simp only [fv_syn_cnnc])))))))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb078SplitAlpha0060 x y g)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb078SplitAlpha0060 x y g)))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
