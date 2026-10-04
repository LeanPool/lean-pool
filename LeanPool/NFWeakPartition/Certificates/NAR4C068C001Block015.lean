/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C068C001Block014

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C068C001Part059`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0175`. -/
@[expose]
noncomputable def nb068SplitAlpha0175 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy501), (nb068AlphaDummy504 f)),
        ((nb068AlphaDummy500), (nb068AlphaDummy503 f)),
        ((nb068AlphaDummy499), (nb068AlphaDummy502 f)),
        ((nb068AlphaDummy497), (nb068AlphaDummy498 f)),
        ((nb068AlphaDummy493), (nb068AlphaDummy495 f)),
        ((nb068AlphaDummy494), (nb068AlphaDummy496 f)),
        ((nb068AlphaDummy486), (nb068AlphaDummy488 f)),
        ((nb068AlphaDummy485), (nb068AlphaDummy487 f)),
        ((nb068AlphaDummy491), (nb068AlphaDummy492 f)),
        ((nb068AlphaDummy489), (nb068AlphaDummy490 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb068AlphaDummy500)) (Class.cv (nb068AlphaDummy501)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb068AlphaDummy499))
            (synCun (Class.cv (nb068AlphaDummy500)) (Class.cv (nb068AlphaDummy501))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb068AlphaDummy503 f))
            (Class.cv (nb068AlphaDummy504 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy502 f))
            (synCun (Class.cv (nb068AlphaDummy503 f))
              (Class.cv (nb068AlphaDummy504 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy500) ≠ (nb068AlphaDummy507) from (by
                              unfold nb068AlphaDummy507;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0526) 0))))
                          (show (nb068AlphaDummy503 f) ≠ (nb068AlphaDummy508 f) from (by
                              unfold nb068AlphaDummy508;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0527 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy500) ≠ (nb068AlphaDummy505) from (by
                                unfold nb068AlphaDummy505;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0524) 0))))
                            (show (nb068AlphaDummy503 f) ≠ (nb068AlphaDummy506 f) from (by
                                unfold nb068AlphaDummy506;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0525 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy493))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy495 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy501) ≠ (nb068AlphaDummy507) from (by
                              unfold nb068AlphaDummy507;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0530) 0))))
                          (show (nb068AlphaDummy504 f) ≠ (nb068AlphaDummy508 f) from (by
                              unfold nb068AlphaDummy508;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0531 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy501) ≠ (nb068AlphaDummy505) from (by
                                unfold nb068AlphaDummy505;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0528) 0))))
                            (show (nb068AlphaDummy504 f) ≠ (nb068AlphaDummy506 f) from (by
                                unfold nb068AlphaDummy506;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0529 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy500) ≠ (nb068AlphaDummy507) from (by
                              unfold nb068AlphaDummy507;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0526) 0))))
                          (show (nb068AlphaDummy503 f) ≠ (nb068AlphaDummy508 f) from (by
                              unfold nb068AlphaDummy508;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0527 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy500) ≠ (nb068AlphaDummy505) from (by
                                unfold nb068AlphaDummy505;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0524) 0))))
                            (show (nb068AlphaDummy503 f) ≠ (nb068AlphaDummy506 f) from (by
                                unfold nb068AlphaDummy506;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0525 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy493))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy495 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy501) ≠ (nb068AlphaDummy507) from (by
                              unfold nb068AlphaDummy507;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0530) 0))))
                          (show (nb068AlphaDummy504 f) ≠ (nb068AlphaDummy508 f) from (by
                              unfold nb068AlphaDummy508;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0531 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy501) ≠ (nb068AlphaDummy505) from (by
                                unfold nb068AlphaDummy505;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0528) 0))))
                            (show (nb068AlphaDummy504 f) ≠ (nb068AlphaDummy506 f) from (by
                                unfold nb068AlphaDummy506;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0529 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb068AlphaDummy501), (nb068AlphaDummy504 f)),
          ((nb068AlphaDummy500), (nb068AlphaDummy503 f)),
          ((nb068AlphaDummy499), (nb068AlphaDummy502 f)),
          ((nb068AlphaDummy497), (nb068AlphaDummy498 f)),
          ((nb068AlphaDummy493), (nb068AlphaDummy495 f)),
          ((nb068AlphaDummy494), (nb068AlphaDummy496 f)),
          ((nb068AlphaDummy486), (nb068AlphaDummy488 f)),
          ((nb068AlphaDummy485), (nb068AlphaDummy487 f)),
          ((nb068AlphaDummy491), (nb068AlphaDummy492 f)),
          ((nb068AlphaDummy489), (nb068AlphaDummy490 f)),
          ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
          ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
          ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
          ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
          ((nb068AlphaDummy001), x),
          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy493))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy495 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068AlphaDummy493))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068AlphaDummy495 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy500) ≠ (nb068AlphaDummy511) from (by
                                unfold nb068AlphaDummy511;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0534) 0))))
                            (show (nb068AlphaDummy503 f) ≠ (nb068AlphaDummy512 f) from (by
                                unfold nb068AlphaDummy512;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0535 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy500) ≠ (nb068AlphaDummy509) from (by
                                  unfold nb068AlphaDummy509;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0532) 0))))
                              (show (nb068AlphaDummy503 f) ≠ (nb068AlphaDummy510 f) from
                                (by
                                  unfold nb068AlphaDummy510;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0533 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy493))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy495 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy500) ≠ (nb068AlphaDummy511) from (by
                                unfold nb068AlphaDummy511;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0534) 0))))
                            (show (nb068AlphaDummy503 f) ≠ (nb068AlphaDummy512 f) from (by
                                unfold nb068AlphaDummy512;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0535 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy500) ≠ (nb068AlphaDummy509) from (by
                                  unfold nb068AlphaDummy509;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0532) 0))))
                              (show (nb068AlphaDummy503 f) ≠ (nb068AlphaDummy510 f) from
                                (by
                                  unfold nb068AlphaDummy510;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0533 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy493))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy495 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy501) ≠ (nb068AlphaDummy513) from (by
                                unfold nb068AlphaDummy513;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0538) 0))))
                            (show (nb068AlphaDummy504 f) ≠ (nb068AlphaDummy514 f) from (by
                                unfold nb068AlphaDummy514;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0539 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy501) ≠ (nb068AlphaDummy509) from (by
                                  unfold nb068AlphaDummy509;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0536) 0))))
                              (show (nb068AlphaDummy504 f) ≠ (nb068AlphaDummy510 f) from
                                (by
                                  unfold nb068AlphaDummy510;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0537 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy501) ≠ (nb068AlphaDummy513) from (by
                                unfold nb068AlphaDummy513;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0538) 0))))
                            (show (nb068AlphaDummy504 f) ≠ (nb068AlphaDummy514 f) from (by
                                unfold nb068AlphaDummy514;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0539 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy501) ≠ (nb068AlphaDummy509) from (by
                                  unfold nb068AlphaDummy509;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0536) 0))))
                              (show (nb068AlphaDummy504 f) ≠ (nb068AlphaDummy510 f) from
                                (by
                                  unfold nb068AlphaDummy510;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0537 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0176`. -/
@[expose]
noncomputable def nb068SplitAlpha0176 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy486), (nb068AlphaDummy488 f)),
        ((nb068AlphaDummy485), (nb068AlphaDummy487 f)),
        ((nb068AlphaDummy491), (nb068AlphaDummy492 f)),
        ((nb068AlphaDummy489), (nb068AlphaDummy490 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.classEq (Class.cv (nb068AlphaDummy485))
        (synCphi (Class.cv (nb068AlphaDummy486))))
      (Wff.classEq (Class.cv (nb068AlphaDummy487 f))
        (synCphi (Class.cv (nb068AlphaDummy488 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb068AlphaDummy329))).fv ∪ ((Class.cv (nb068AlphaDummy328))).fv)
          (by decide)) (freshVar_injective (((Class.cv (nb068AlphaDummy332 f))).fv ∪
            ((Class.cv (nb068AlphaDummy331 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (show (nb068AlphaDummy486) ≠ (nb068AlphaDummy493) from (by
                    unfold nb068AlphaDummy493;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0518) 0))))
                (show (nb068AlphaDummy488 f) ≠ (nb068AlphaDummy495 f) from (by
                    unfold nb068AlphaDummy495;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0519 f) 0))))
                (TAlphaVar.there (show (nb068AlphaDummy486) ≠ (nb068AlphaDummy494) from
                    (by
                      unfold nb068AlphaDummy494;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0518) 1))))
                  (show (nb068AlphaDummy488 f) ≠ (nb068AlphaDummy496 f) from (by
                      unfold nb068AlphaDummy496;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0519 f) 1))))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb068AlphaDummy486))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb068AlphaDummy488 f))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb068AlphaDummy493) ≠ (nb068AlphaDummy500) from
                                    (by
                                      unfold nb068AlphaDummy500;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0522)
                                              1)))) (show
                                    (nb068AlphaDummy495 f) ≠ (nb068AlphaDummy503 f) from
                                    (by
                                      unfold nb068AlphaDummy503;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0523 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb068AlphaDummy493) ≠ (nb068AlphaDummy499) from (by
                                        unfold nb068AlphaDummy499;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0522)
                                                0)))) (show (nb068AlphaDummy495 f) ≠
                                        (nb068AlphaDummy502 f) from (by
                                        unfold nb068AlphaDummy502;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0523 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy493) ≠ (nb068AlphaDummy497) from
                                        (by
                                          unfold nb068AlphaDummy497;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0520)
                                                  0)))) (show (nb068AlphaDummy495 f) ≠
        (nb068AlphaDummy498 f) from (by
                                          unfold nb068AlphaDummy498;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0521 f) 0))))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.reflOfClosed
                                    [((nb068AlphaDummy501), (nb068AlphaDummy504 f)),
                                      ((nb068AlphaDummy500), (nb068AlphaDummy503 f)),
                                      ((nb068AlphaDummy499), (nb068AlphaDummy502 f)),
                                      ((nb068AlphaDummy497), (nb068AlphaDummy498 f)),
                                      ((nb068AlphaDummy493), (nb068AlphaDummy495 f)),
                                      ((nb068AlphaDummy494), (nb068AlphaDummy496 f)),
                                      ((nb068AlphaDummy486), (nb068AlphaDummy488 f)),
                                      ((nb068AlphaDummy485), (nb068AlphaDummy487 f)),
                                      ((nb068AlphaDummy491), (nb068AlphaDummy492 f)),
                                      ((nb068AlphaDummy489), (nb068AlphaDummy490 f)),
                                      ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                                      ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                                      ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                                      ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                                      ((nb068AlphaDummy000), f),
                                      ((nb068AlphaDummy002), y),
                                      ((nb068AlphaDummy001), x), ((nb068AlphaDummy003),
                                        (nb068AlphaDummy004 x y f))]
                                    (synC1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb068SplitAlpha0175 x y f))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (show (nb068AlphaDummy493) ≠ (nb068AlphaDummy497) from (by
                              unfold nb068AlphaDummy497;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0520) 0))))
                          (show (nb068AlphaDummy495 f) ≠ (nb068AlphaDummy498 f) from (by
                              unfold nb068AlphaDummy498;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0521 f) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb068AlphaDummy497), (nb068AlphaDummy498 f)),
                          ((nb068AlphaDummy493), (nb068AlphaDummy495 f)),
                          ((nb068AlphaDummy494), (nb068AlphaDummy496 f)),
                          ((nb068AlphaDummy486), (nb068AlphaDummy488 f)),
                          ((nb068AlphaDummy485), (nb068AlphaDummy487 f)),
                          ((nb068AlphaDummy491), (nb068AlphaDummy492 f)),
                          ((nb068AlphaDummy489), (nb068AlphaDummy490 f)),
                          ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                          ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                          ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                          ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                          ((nb068AlphaDummy001), x),
                          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb068AlphaDummy493) ≠ (nb068AlphaDummy497) from (by
                            unfold nb068AlphaDummy497;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0520) 0))))
                        (show (nb068AlphaDummy495 f) ≠ (nb068AlphaDummy498 f) from (by
                            unfold nb068AlphaDummy498;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0521 f) 0))))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (show (nb068AlphaDummy493) ≠ (nb068AlphaDummy497) from (by
                              unfold nb068AlphaDummy497;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0520) 0))))
                          (show (nb068AlphaDummy495 f) ≠ (nb068AlphaDummy498 f) from (by
                              unfold nb068AlphaDummy498;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0521 f) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb068AlphaDummy497), (nb068AlphaDummy498 f)),
                          ((nb068AlphaDummy493), (nb068AlphaDummy495 f)),
                          ((nb068AlphaDummy494), (nb068AlphaDummy496 f)),
                          ((nb068AlphaDummy486), (nb068AlphaDummy488 f)),
                          ((nb068AlphaDummy485), (nb068AlphaDummy487 f)),
                          ((nb068AlphaDummy491), (nb068AlphaDummy492 f)),
                          ((nb068AlphaDummy489), (nb068AlphaDummy490 f)),
                          ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                          ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                          ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                          ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                          ((nb068AlphaDummy001), x),
                          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0177`. -/
@[expose]
noncomputable def nb068SplitAlpha0177 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy501), (nb068AlphaDummy504 f)),
        ((nb068AlphaDummy500), (nb068AlphaDummy503 f)),
        ((nb068AlphaDummy499), (nb068AlphaDummy502 f)),
        ((nb068AlphaDummy497), (nb068AlphaDummy498 f)),
        ((nb068AlphaDummy493), (nb068AlphaDummy495 f)),
        ((nb068AlphaDummy494), (nb068AlphaDummy496 f)),
        ((nb068AlphaDummy519), (nb068AlphaDummy520 f)),
        ((nb068AlphaDummy517), (nb068AlphaDummy518 f)),
        ((nb068AlphaDummy486), (nb068AlphaDummy488 f)),
        ((nb068AlphaDummy485), (nb068AlphaDummy487 f)),
        ((nb068AlphaDummy515), (nb068AlphaDummy516 f)),
        ((nb068AlphaDummy489), (nb068AlphaDummy490 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb068AlphaDummy500)) (Class.cv (nb068AlphaDummy501)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb068AlphaDummy499))
            (synCun (Class.cv (nb068AlphaDummy500)) (Class.cv (nb068AlphaDummy501))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb068AlphaDummy503 f))
            (Class.cv (nb068AlphaDummy504 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy502 f))
            (synCun (Class.cv (nb068AlphaDummy503 f))
              (Class.cv (nb068AlphaDummy504 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy500) ≠ (nb068AlphaDummy507) from (by
                              unfold nb068AlphaDummy507;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0526) 0))))
                          (show (nb068AlphaDummy503 f) ≠ (nb068AlphaDummy508 f) from (by
                              unfold nb068AlphaDummy508;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0527 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy500) ≠ (nb068AlphaDummy505) from (by
                                unfold nb068AlphaDummy505;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0524) 0))))
                            (show (nb068AlphaDummy503 f) ≠ (nb068AlphaDummy506 f) from (by
                                unfold nb068AlphaDummy506;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0525 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy493))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy495 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy501) ≠ (nb068AlphaDummy507) from (by
                              unfold nb068AlphaDummy507;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0530) 0))))
                          (show (nb068AlphaDummy504 f) ≠ (nb068AlphaDummy508 f) from (by
                              unfold nb068AlphaDummy508;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0531 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy501) ≠ (nb068AlphaDummy505) from (by
                                unfold nb068AlphaDummy505;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0528) 0))))
                            (show (nb068AlphaDummy504 f) ≠ (nb068AlphaDummy506 f) from (by
                                unfold nb068AlphaDummy506;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0529 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy500) ≠ (nb068AlphaDummy507) from (by
                              unfold nb068AlphaDummy507;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0526) 0))))
                          (show (nb068AlphaDummy503 f) ≠ (nb068AlphaDummy508 f) from (by
                              unfold nb068AlphaDummy508;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0527 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy500) ≠ (nb068AlphaDummy505) from (by
                                unfold nb068AlphaDummy505;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0524) 0))))
                            (show (nb068AlphaDummy503 f) ≠ (nb068AlphaDummy506 f) from (by
                                unfold nb068AlphaDummy506;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0525 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy493))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy495 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy501) ≠ (nb068AlphaDummy507) from (by
                              unfold nb068AlphaDummy507;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0530) 0))))
                          (show (nb068AlphaDummy504 f) ≠ (nb068AlphaDummy508 f) from (by
                              unfold nb068AlphaDummy508;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0531 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy501) ≠ (nb068AlphaDummy505) from (by
                                unfold nb068AlphaDummy505;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0528) 0))))
                            (show (nb068AlphaDummy504 f) ≠ (nb068AlphaDummy506 f) from (by
                                unfold nb068AlphaDummy506;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0529 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb068AlphaDummy501), (nb068AlphaDummy504 f)),
          ((nb068AlphaDummy500), (nb068AlphaDummy503 f)),
          ((nb068AlphaDummy499), (nb068AlphaDummy502 f)),
          ((nb068AlphaDummy497), (nb068AlphaDummy498 f)),
          ((nb068AlphaDummy493), (nb068AlphaDummy495 f)),
          ((nb068AlphaDummy494), (nb068AlphaDummy496 f)),
          ((nb068AlphaDummy519), (nb068AlphaDummy520 f)),
          ((nb068AlphaDummy517), (nb068AlphaDummy518 f)),
          ((nb068AlphaDummy486), (nb068AlphaDummy488 f)),
          ((nb068AlphaDummy485), (nb068AlphaDummy487 f)),
          ((nb068AlphaDummy515), (nb068AlphaDummy516 f)),
          ((nb068AlphaDummy489), (nb068AlphaDummy490 f)),
          ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
          ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
          ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
          ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
          ((nb068AlphaDummy001), x),
          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy493))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy495 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068AlphaDummy493))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068AlphaDummy495 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy500) ≠ (nb068AlphaDummy511) from (by
                                unfold nb068AlphaDummy511;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0534) 0))))
                            (show (nb068AlphaDummy503 f) ≠ (nb068AlphaDummy512 f) from (by
                                unfold nb068AlphaDummy512;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0535 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy500) ≠ (nb068AlphaDummy509) from (by
                                  unfold nb068AlphaDummy509;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0532) 0))))
                              (show (nb068AlphaDummy503 f) ≠ (nb068AlphaDummy510 f) from
                                (by
                                  unfold nb068AlphaDummy510;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0533 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy493))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy495 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy500) ≠ (nb068AlphaDummy511) from (by
                                unfold nb068AlphaDummy511;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0534) 0))))
                            (show (nb068AlphaDummy503 f) ≠ (nb068AlphaDummy512 f) from (by
                                unfold nb068AlphaDummy512;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0535 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy500) ≠ (nb068AlphaDummy509) from (by
                                  unfold nb068AlphaDummy509;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0532) 0))))
                              (show (nb068AlphaDummy503 f) ≠ (nb068AlphaDummy510 f) from
                                (by
                                  unfold nb068AlphaDummy510;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0533 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy493))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy495 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy501) ≠ (nb068AlphaDummy513) from (by
                                unfold nb068AlphaDummy513;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0538) 0))))
                            (show (nb068AlphaDummy504 f) ≠ (nb068AlphaDummy514 f) from (by
                                unfold nb068AlphaDummy514;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0539 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy501) ≠ (nb068AlphaDummy509) from (by
                                  unfold nb068AlphaDummy509;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0536) 0))))
                              (show (nb068AlphaDummy504 f) ≠ (nb068AlphaDummy510 f) from
                                (by
                                  unfold nb068AlphaDummy510;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0537 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy501) ≠ (nb068AlphaDummy513) from (by
                                unfold nb068AlphaDummy513;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0538) 0))))
                            (show (nb068AlphaDummy504 f) ≠ (nb068AlphaDummy514 f) from (by
                                unfold nb068AlphaDummy514;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0539 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy501) ≠ (nb068AlphaDummy509) from (by
                                  unfold nb068AlphaDummy509;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0536) 0))))
                              (show (nb068AlphaDummy504 f) ≠ (nb068AlphaDummy510 f) from
                                (by
                                  unfold nb068AlphaDummy510;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0537 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0178`. -/
@[expose]
noncomputable def nb068SplitAlpha0178 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy493), (nb068AlphaDummy495 f)),
        ((nb068AlphaDummy494), (nb068AlphaDummy496 f)),
        ((nb068AlphaDummy519), (nb068AlphaDummy520 f)),
        ((nb068AlphaDummy517), (nb068AlphaDummy518 f)),
        ((nb068AlphaDummy486), (nb068AlphaDummy488 f)),
        ((nb068AlphaDummy485), (nb068AlphaDummy487 f)),
        ((nb068AlphaDummy515), (nb068AlphaDummy516 f)),
        ((nb068AlphaDummy489), (nb068AlphaDummy490 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy493))
          (Class.cv (nb068AlphaDummy486))) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy494))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy493)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy493)) (synC1c))
              (Class.cv (nb068AlphaDummy493))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy495 f))
          (Class.cv (nb068AlphaDummy488 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy496 f))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy495 f)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy495 f)) (synC1c))
              (Class.cv (nb068AlphaDummy495 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy486) ≠ (nb068AlphaDummy493) from (by
              unfold nb068AlphaDummy493;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0518) 0))))
          (show (nb068AlphaDummy488 f) ≠ (nb068AlphaDummy495 f) from (by
              unfold nb068AlphaDummy495;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0519 f) 0))))
          (TAlphaVar.there (show (nb068AlphaDummy486) ≠ (nb068AlphaDummy494) from (by
                unfold nb068AlphaDummy494;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0518) 1))))
            (show (nb068AlphaDummy488 f) ≠ (nb068AlphaDummy496 f) from (by
                unfold nb068AlphaDummy496;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0519 f) 1))))
            (TAlphaVar.there (show (nb068AlphaDummy486) ≠ (nb068AlphaDummy519) from (by
                  unfold nb068AlphaDummy519;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0548) 0))))
              (show (nb068AlphaDummy488 f) ≠ (nb068AlphaDummy520 f) from (by
                  unfold nb068AlphaDummy520;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0549 f) 0))))
              (TAlphaVar.there (show (nb068AlphaDummy486) ≠ (nb068AlphaDummy517) from (by
                    unfold nb068AlphaDummy517;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0546) 0))))
                (show (nb068AlphaDummy488 f) ≠ (nb068AlphaDummy518 f) from (by
                    unfold nb068AlphaDummy518;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0547 f) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy486))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb068AlphaDummy488 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068AlphaDummy493) ≠ (nb068AlphaDummy500) from (by
                                  unfold nb068AlphaDummy500;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0522) 1))))
                              (show (nb068AlphaDummy495 f) ≠ (nb068AlphaDummy503 f) from
                                (by
                                  unfold nb068AlphaDummy503;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0523 f) 1))))
                              (TAlphaVar.there
                                (show (nb068AlphaDummy493) ≠ (nb068AlphaDummy499) from (by
                                    unfold nb068AlphaDummy499;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0522) 0)))) (show
                                  (nb068AlphaDummy495 f) ≠ (nb068AlphaDummy502 f) from (by
                                    unfold nb068AlphaDummy502;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0523 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb068AlphaDummy493) ≠ (nb068AlphaDummy497) from
                                    (by
                                      unfold nb068AlphaDummy497;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0520)
                                              0)))) (show
                                    (nb068AlphaDummy495 f) ≠ (nb068AlphaDummy498 f) from
                                    (by
                                      unfold nb068AlphaDummy498;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0521 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb068AlphaDummy501), (nb068AlphaDummy504 f)),
                                  ((nb068AlphaDummy500), (nb068AlphaDummy503 f)),
                                  ((nb068AlphaDummy499), (nb068AlphaDummy502 f)),
                                  ((nb068AlphaDummy497), (nb068AlphaDummy498 f)),
                                  ((nb068AlphaDummy493), (nb068AlphaDummy495 f)),
                                  ((nb068AlphaDummy494), (nb068AlphaDummy496 f)),
                                  ((nb068AlphaDummy519), (nb068AlphaDummy520 f)),
                                  ((nb068AlphaDummy517), (nb068AlphaDummy518 f)),
                                  ((nb068AlphaDummy486), (nb068AlphaDummy488 f)),
                                  ((nb068AlphaDummy485), (nb068AlphaDummy487 f)),
                                  ((nb068AlphaDummy515), (nb068AlphaDummy516 f)),
                                  ((nb068AlphaDummy489), (nb068AlphaDummy490 f)),
                                  ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                                  ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                                  ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                                  ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                                  ((nb068AlphaDummy001), x), ((nb068AlphaDummy003),
                                    (nb068AlphaDummy004 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb068SplitAlpha0177 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb068AlphaDummy493) ≠ (nb068AlphaDummy497) from (by
                          unfold nb068AlphaDummy497;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0520) 0))))
                      (show (nb068AlphaDummy495 f) ≠ (nb068AlphaDummy498 f) from (by
                          unfold nb068AlphaDummy498;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0521 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb068AlphaDummy497), (nb068AlphaDummy498 f)),
                      ((nb068AlphaDummy493), (nb068AlphaDummy495 f)),
                      ((nb068AlphaDummy494), (nb068AlphaDummy496 f)),
                      ((nb068AlphaDummy519), (nb068AlphaDummy520 f)),
                      ((nb068AlphaDummy517), (nb068AlphaDummy518 f)),
                      ((nb068AlphaDummy486), (nb068AlphaDummy488 f)),
                      ((nb068AlphaDummy485), (nb068AlphaDummy487 f)),
                      ((nb068AlphaDummy515), (nb068AlphaDummy516 f)),
                      ((nb068AlphaDummy489), (nb068AlphaDummy490 f)),
                      ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                      ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                      ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                      ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                      ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                      ((nb068AlphaDummy001), x),
                      ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068AlphaDummy493) ≠ (nb068AlphaDummy497) from
                      (by
                        unfold nb068AlphaDummy497;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0520) 0))))
                    (show (nb068AlphaDummy495 f) ≠ (nb068AlphaDummy498 f) from (by
                        unfold nb068AlphaDummy498;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0521 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068AlphaDummy493) ≠ (nb068AlphaDummy497) from (by
                          unfold nb068AlphaDummy497;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0520) 0))))
                      (show (nb068AlphaDummy495 f) ≠ (nb068AlphaDummy498 f) from (by
                          unfold nb068AlphaDummy498;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0521 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb068AlphaDummy497), (nb068AlphaDummy498 f)),
                      ((nb068AlphaDummy493), (nb068AlphaDummy495 f)),
                      ((nb068AlphaDummy494), (nb068AlphaDummy496 f)),
                      ((nb068AlphaDummy519), (nb068AlphaDummy520 f)),
                      ((nb068AlphaDummy517), (nb068AlphaDummy518 f)),
                      ((nb068AlphaDummy486), (nb068AlphaDummy488 f)),
                      ((nb068AlphaDummy485), (nb068AlphaDummy487 f)),
                      ((nb068AlphaDummy515), (nb068AlphaDummy516 f)),
                      ((nb068AlphaDummy489), (nb068AlphaDummy490 f)),
                      ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                      ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                      ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                      ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                      ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                      ((nb068AlphaDummy001), x),
                      ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0179`. -/
@[expose]
noncomputable def nb068SplitAlpha0179 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy515), (nb068AlphaDummy516 f)),
        ((nb068AlphaDummy489), (nb068AlphaDummy490 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy515))
          (Class.cab (nb068AlphaDummy485)
            (synWrex (nb068AlphaDummy486) (Class.cv (nb068AlphaDummy328))
              (Wff.classEq (Class.cv (nb068AlphaDummy485))
                (synCun (synCphi (Class.cv (nb068AlphaDummy486))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb068AlphaDummy515))
            (Class.cab (nb068AlphaDummy485)
              (synWrex (nb068AlphaDummy486) (Class.cv (nb068AlphaDummy328))
                (Wff.classEq (Class.cv (nb068AlphaDummy485))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy486)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy516 f))
          (Class.cab (nb068AlphaDummy487 f)
            (synWrex (nb068AlphaDummy488 f) (Class.cv (nb068AlphaDummy331 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy487 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy488 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb068AlphaDummy516 f))
            (Class.cab (nb068AlphaDummy487 f)
              (synWrex (nb068AlphaDummy488 f) (Class.cv (nb068AlphaDummy331 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy487 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy488 f)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb068AlphaDummy328) ≠ (nb068AlphaDummy486) from
                    (by
                      unfold nb068AlphaDummy486;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0540) 1))))
                  (show (nb068AlphaDummy331 f) ≠ (nb068AlphaDummy488 f) from (by
                      unfold nb068AlphaDummy488;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0542 f) 1))))
                  (TAlphaVar.there (show (nb068AlphaDummy328) ≠ (nb068AlphaDummy485) from
                      (by
                        unfold nb068AlphaDummy485;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0540) 0))))
                    (show (nb068AlphaDummy331 f) ≠ (nb068AlphaDummy487 f) from (by
                        unfold nb068AlphaDummy487;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0542 f) 0)))) (TAlphaVar.there
                      (show (nb068AlphaDummy328) ≠ (nb068AlphaDummy515) from (by
                          unfold nb068AlphaDummy515;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0544) 0))))
                      (show (nb068AlphaDummy331 f) ≠ (nb068AlphaDummy516 f) from (by
                          unfold nb068AlphaDummy516;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0545 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy328) ≠ (nb068AlphaDummy489) from (by
                            unfold nb068AlphaDummy489;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0541) 0))))
                        (show (nb068AlphaDummy331 f) ≠ (nb068AlphaDummy490 f) from (by
                            unfold nb068AlphaDummy490;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0543 f) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((synCcnv (Class.cv (nb068AlphaDummy000)))).fv ∪ ((synCcnv
                                  (synCcnv (Class.cv (nb068AlphaDummy000))))).fv)
                            (by decide)) (freshVar_injective (((synCcnv (Class.cv f))).fv ∪
                              ((synCcnv (synCcnv (Class.cv f)))).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb068AlphaDummy329))).fv ∪
                      ((Class.cv (nb068AlphaDummy328))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb068AlphaDummy332 f))).fv ∪
                      ((Class.cv (nb068AlphaDummy331 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068SplitAlpha0178 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068SplitAlpha0178 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb068AlphaDummy517), (nb068AlphaDummy518 f)),
                          ((nb068AlphaDummy486), (nb068AlphaDummy488 f)),
                          ((nb068AlphaDummy485), (nb068AlphaDummy487 f)),
                          ((nb068AlphaDummy515), (nb068AlphaDummy516 f)),
                          ((nb068AlphaDummy489), (nb068AlphaDummy490 f)),
                          ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                          ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                          ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                          ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                          ((nb068AlphaDummy001), x),
                          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068AlphaDummy328) ≠ (nb068AlphaDummy486) from
                      (by
                        unfold nb068AlphaDummy486;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0540) 1))))
                    (show (nb068AlphaDummy331 f) ≠ (nb068AlphaDummy488 f) from (by
                        unfold nb068AlphaDummy488;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0542 f) 1)))) (TAlphaVar.there
                      (show (nb068AlphaDummy328) ≠ (nb068AlphaDummy485) from (by
                          unfold nb068AlphaDummy485;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0540) 0))))
                      (show (nb068AlphaDummy331 f) ≠ (nb068AlphaDummy487 f) from (by
                          unfold nb068AlphaDummy487;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0542 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy328) ≠ (nb068AlphaDummy515) from (by
                            unfold nb068AlphaDummy515;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0544) 0))))
                        (show (nb068AlphaDummy331 f) ≠ (nb068AlphaDummy516 f) from (by
                            unfold nb068AlphaDummy516;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0545 f) 0))))
                        (TAlphaVar.there
                          (show (nb068AlphaDummy328) ≠ (nb068AlphaDummy489) from (by
                              unfold nb068AlphaDummy489;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0541) 0))))
                          (show (nb068AlphaDummy331 f) ≠ (nb068AlphaDummy490 f) from (by
                              unfold nb068AlphaDummy490;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0543 f) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((synCcnv (Class.cv (nb068AlphaDummy000)))).fv ∪ ((synCcnv
                                    (synCcnv (Class.cv (nb068AlphaDummy000))))).fv)
                              (by decide)) (freshVar_injective (((synCcnv (Class.cv f))).fv ∪
                                ((synCcnv (synCcnv (Class.cv f)))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb068AlphaDummy329))).fv ∪
                        ((Class.cv (nb068AlphaDummy328))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb068AlphaDummy332 f))).fv ∪
                        ((Class.cv (nb068AlphaDummy331 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068SplitAlpha0178 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068SplitAlpha0178 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb068AlphaDummy517), (nb068AlphaDummy518 f)),
                            ((nb068AlphaDummy486), (nb068AlphaDummy488 f)),
                            ((nb068AlphaDummy485), (nb068AlphaDummy487 f)),
                            ((nb068AlphaDummy515), (nb068AlphaDummy516 f)),
                            ((nb068AlphaDummy489), (nb068AlphaDummy490 f)),
                            ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                            ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                            ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                            ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                            ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                            ((nb068AlphaDummy001), x),
                            ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part060`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0180`. -/
@[expose]
noncomputable def nb068SplitAlpha0180 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy147), (nb068AlphaDummy150 f)),
        ((nb068AlphaDummy146), (nb068AlphaDummy149 f)),
        ((nb068AlphaDummy145), (nb068AlphaDummy148 f)),
        ((nb068AlphaDummy143), (nb068AlphaDummy144 f)),
        ((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
        ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
        ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
        ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
        ((nb068AlphaDummy137), (nb068AlphaDummy138 f)),
        ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
        ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb068AlphaDummy146)) (Class.cv (nb068AlphaDummy147)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb068AlphaDummy145))
            (synCun (Class.cv (nb068AlphaDummy146)) (Class.cv (nb068AlphaDummy147))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb068AlphaDummy149 f))
            (Class.cv (nb068AlphaDummy150 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy148 f))
            (synCun (Class.cv (nb068AlphaDummy149 f))
              (Class.cv (nb068AlphaDummy150 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy153) from (by
                              unfold nb068AlphaDummy153;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0140) 0))))
                          (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy154 f) from (by
                              unfold nb068AlphaDummy154;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0141 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy151) from (by
                                unfold nb068AlphaDummy151;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0138) 0))))
                            (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy152 f) from (by
                                unfold nb068AlphaDummy152;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0139 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy153) from (by
                              unfold nb068AlphaDummy153;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0144) 0))))
                          (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy154 f) from (by
                              unfold nb068AlphaDummy154;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0145 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy151) from (by
                                unfold nb068AlphaDummy151;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0142) 0))))
                            (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy152 f) from (by
                                unfold nb068AlphaDummy152;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0143 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy153) from (by
                              unfold nb068AlphaDummy153;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0140) 0))))
                          (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy154 f) from (by
                              unfold nb068AlphaDummy154;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0141 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy151) from (by
                                unfold nb068AlphaDummy151;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0138) 0))))
                            (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy152 f) from (by
                                unfold nb068AlphaDummy152;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0139 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy153) from (by
                              unfold nb068AlphaDummy153;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0144) 0))))
                          (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy154 f) from (by
                              unfold nb068AlphaDummy154;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0145 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy151) from (by
                                unfold nb068AlphaDummy151;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0142) 0))))
                            (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy152 f) from (by
                                unfold nb068AlphaDummy152;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0143 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb068AlphaDummy147), (nb068AlphaDummy150 f)),
          ((nb068AlphaDummy146), (nb068AlphaDummy149 f)),
          ((nb068AlphaDummy145), (nb068AlphaDummy148 f)),
          ((nb068AlphaDummy143), (nb068AlphaDummy144 f)),
          ((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
          ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
          ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
          ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
          ((nb068AlphaDummy137), (nb068AlphaDummy138 f)),
          ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
          ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
          ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
          ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
          ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
          ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
          ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
          ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
          ((nb068AlphaDummy001), x),
          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy157) from (by
                                unfold nb068AlphaDummy157;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0148) 0))))
                            (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy158 f) from (by
                                unfold nb068AlphaDummy158;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0149 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy155) from (by
                                  unfold nb068AlphaDummy155;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0146) 0))))
                              (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy156 f) from
                                (by
                                  unfold nb068AlphaDummy156;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0147 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy157) from (by
                                unfold nb068AlphaDummy157;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0148) 0))))
                            (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy158 f) from (by
                                unfold nb068AlphaDummy158;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0149 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy155) from (by
                                  unfold nb068AlphaDummy155;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0146) 0))))
                              (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy156 f) from
                                (by
                                  unfold nb068AlphaDummy156;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0147 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy159) from (by
                                unfold nb068AlphaDummy159;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0152) 0))))
                            (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy160 f) from (by
                                unfold nb068AlphaDummy160;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0153 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy155) from (by
                                  unfold nb068AlphaDummy155;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0150) 0))))
                              (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy156 f) from
                                (by
                                  unfold nb068AlphaDummy156;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0151 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy159) from (by
                                unfold nb068AlphaDummy159;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0152) 0))))
                            (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy160 f) from (by
                                unfold nb068AlphaDummy160;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0153 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy155) from (by
                                  unfold nb068AlphaDummy155;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0150) 0))))
                              (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy156 f) from
                                (by
                                  unfold nb068AlphaDummy156;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0151 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0181`. -/
@[expose]
noncomputable def nb068SplitAlpha0181 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
        ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
        ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
        ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
        ((nb068AlphaDummy137), (nb068AlphaDummy138 f)),
        ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
        ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy139))
          (Class.cv (nb068AlphaDummy132))) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy140))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy139)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy139)) (synC1c))
              (Class.cv (nb068AlphaDummy139))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy141 f))
          (Class.cv (nb068AlphaDummy134 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy142 f))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy141 f)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy141 f)) (synC1c))
              (Class.cv (nb068AlphaDummy141 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy132) ≠ (nb068AlphaDummy139) from (by
              unfold nb068AlphaDummy139;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0132) 0))))
          (show (nb068AlphaDummy134 f) ≠ (nb068AlphaDummy141 f) from (by
              unfold nb068AlphaDummy141;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0133 f) 0))))
          (TAlphaVar.there (show (nb068AlphaDummy132) ≠ (nb068AlphaDummy140) from (by
                unfold nb068AlphaDummy140;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0132) 1))))
            (show (nb068AlphaDummy134 f) ≠ (nb068AlphaDummy142 f) from (by
                unfold nb068AlphaDummy142;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0133 f) 1))))
            (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy132))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb068AlphaDummy134 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy146) from (by
                                  unfold nb068AlphaDummy146;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0136) 1))))
                              (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy149 f) from
                                (by
                                  unfold nb068AlphaDummy149;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0137 f) 1))))
                              (TAlphaVar.there
                                (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy145) from (by
                                    unfold nb068AlphaDummy145;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0136) 0)))) (show
                                  (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy148 f) from (by
                                    unfold nb068AlphaDummy148;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0137 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy143) from
                                    (by
                                      unfold nb068AlphaDummy143;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0134)
                                              0)))) (show
                                    (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy144 f) from
                                    (by
                                      unfold nb068AlphaDummy144;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0135 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb068AlphaDummy147), (nb068AlphaDummy150 f)),
                                  ((nb068AlphaDummy146), (nb068AlphaDummy149 f)),
                                  ((nb068AlphaDummy145), (nb068AlphaDummy148 f)),
                                  ((nb068AlphaDummy143), (nb068AlphaDummy144 f)),
                                  ((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
                                  ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
                                  ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
                                  ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
                                  ((nb068AlphaDummy137), (nb068AlphaDummy138 f)),
                                  ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
                                  ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                                  ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                                  ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                                  ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                                  ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                                  ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                                  ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                                  ((nb068AlphaDummy001), x), ((nb068AlphaDummy003),
                                    (nb068AlphaDummy004 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb068SplitAlpha0180 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy143) from (by
                          unfold nb068AlphaDummy143;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0134) 0))))
                      (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy144 f) from (by
                          unfold nb068AlphaDummy144;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb068AlphaDummy143), (nb068AlphaDummy144 f)),
                      ((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
                      ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
                      ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
                      ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
                      ((nb068AlphaDummy137), (nb068AlphaDummy138 f)),
                      ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
                      ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                      ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                      ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                      ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                      ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                      ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                      ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                      ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                      ((nb068AlphaDummy001), x),
                      ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy143) from
                      (by
                        unfold nb068AlphaDummy143;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0134) 0))))
                    (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy144 f) from (by
                        unfold nb068AlphaDummy144;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy143) from (by
                          unfold nb068AlphaDummy143;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0134) 0))))
                      (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy144 f) from (by
                          unfold nb068AlphaDummy144;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb068AlphaDummy143), (nb068AlphaDummy144 f)),
                      ((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
                      ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
                      ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
                      ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
                      ((nb068AlphaDummy137), (nb068AlphaDummy138 f)),
                      ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
                      ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                      ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                      ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                      ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                      ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                      ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                      ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                      ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                      ((nb068AlphaDummy001), x),
                      ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0182`. -/
@[expose]
noncomputable def nb068SplitAlpha0182 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy147), (nb068AlphaDummy150 f)),
        ((nb068AlphaDummy146), (nb068AlphaDummy149 f)),
        ((nb068AlphaDummy145), (nb068AlphaDummy148 f)),
        ((nb068AlphaDummy143), (nb068AlphaDummy144 f)),
        ((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
        ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
        ((nb068AlphaDummy165), (nb068AlphaDummy166 f)),
        ((nb068AlphaDummy163), (nb068AlphaDummy164 f)),
        ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
        ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
        ((nb068AlphaDummy161), (nb068AlphaDummy162 f)),
        ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
        ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb068AlphaDummy146)) (Class.cv (nb068AlphaDummy147)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb068AlphaDummy145))
            (synCun (Class.cv (nb068AlphaDummy146)) (Class.cv (nb068AlphaDummy147))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb068AlphaDummy149 f))
            (Class.cv (nb068AlphaDummy150 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy148 f))
            (synCun (Class.cv (nb068AlphaDummy149 f))
              (Class.cv (nb068AlphaDummy150 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy153) from (by
                              unfold nb068AlphaDummy153;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0140) 0))))
                          (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy154 f) from (by
                              unfold nb068AlphaDummy154;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0141 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy151) from (by
                                unfold nb068AlphaDummy151;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0138) 0))))
                            (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy152 f) from (by
                                unfold nb068AlphaDummy152;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0139 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy153) from (by
                              unfold nb068AlphaDummy153;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0144) 0))))
                          (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy154 f) from (by
                              unfold nb068AlphaDummy154;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0145 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy151) from (by
                                unfold nb068AlphaDummy151;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0142) 0))))
                            (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy152 f) from (by
                                unfold nb068AlphaDummy152;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0143 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy153) from (by
                              unfold nb068AlphaDummy153;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0140) 0))))
                          (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy154 f) from (by
                              unfold nb068AlphaDummy154;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0141 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy151) from (by
                                unfold nb068AlphaDummy151;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0138) 0))))
                            (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy152 f) from (by
                                unfold nb068AlphaDummy152;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0139 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy153) from (by
                              unfold nb068AlphaDummy153;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0144) 0))))
                          (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy154 f) from (by
                              unfold nb068AlphaDummy154;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0145 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy151) from (by
                                unfold nb068AlphaDummy151;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0142) 0))))
                            (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy152 f) from (by
                                unfold nb068AlphaDummy152;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0143 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb068AlphaDummy147), (nb068AlphaDummy150 f)),
          ((nb068AlphaDummy146), (nb068AlphaDummy149 f)),
          ((nb068AlphaDummy145), (nb068AlphaDummy148 f)),
          ((nb068AlphaDummy143), (nb068AlphaDummy144 f)),
          ((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
          ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
          ((nb068AlphaDummy165), (nb068AlphaDummy166 f)),
          ((nb068AlphaDummy163), (nb068AlphaDummy164 f)),
          ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
          ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
          ((nb068AlphaDummy161), (nb068AlphaDummy162 f)),
          ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
          ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
          ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
          ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
          ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
          ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
          ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
          ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
          ((nb068AlphaDummy001), x),
          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy157) from (by
                                unfold nb068AlphaDummy157;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0148) 0))))
                            (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy158 f) from (by
                                unfold nb068AlphaDummy158;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0149 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy155) from (by
                                  unfold nb068AlphaDummy155;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0146) 0))))
                              (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy156 f) from
                                (by
                                  unfold nb068AlphaDummy156;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0147 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy157) from (by
                                unfold nb068AlphaDummy157;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0148) 0))))
                            (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy158 f) from (by
                                unfold nb068AlphaDummy158;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0149 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy155) from (by
                                  unfold nb068AlphaDummy155;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0146) 0))))
                              (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy156 f) from
                                (by
                                  unfold nb068AlphaDummy156;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0147 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy159) from (by
                                unfold nb068AlphaDummy159;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0152) 0))))
                            (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy160 f) from (by
                                unfold nb068AlphaDummy160;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0153 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy155) from (by
                                  unfold nb068AlphaDummy155;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0150) 0))))
                              (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy156 f) from
                                (by
                                  unfold nb068AlphaDummy156;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0151 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy159) from (by
                                unfold nb068AlphaDummy159;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0152) 0))))
                            (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy160 f) from (by
                                unfold nb068AlphaDummy160;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0153 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy155) from (by
                                  unfold nb068AlphaDummy155;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0150) 0))))
                              (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy156 f) from
                                (by
                                  unfold nb068AlphaDummy156;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0151 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0183`. -/
@[expose]
noncomputable def nb068SplitAlpha0183 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
        ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
        ((nb068AlphaDummy165), (nb068AlphaDummy166 f)),
        ((nb068AlphaDummy163), (nb068AlphaDummy164 f)),
        ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
        ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
        ((nb068AlphaDummy161), (nb068AlphaDummy162 f)),
        ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
        ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.classEq (Class.cv (nb068AlphaDummy140))
        (synCif (Wff.classMem (Class.cv (nb068AlphaDummy139)) (synCnnc))
          (synCplc (Class.cv (nb068AlphaDummy139)) (synC1c))
          (Class.cv (nb068AlphaDummy139))))
      (Wff.classEq (Class.cv (nb068AlphaDummy142 f))
        (synCif (Wff.classMem (Class.cv (nb068AlphaDummy141 f)) (synCnnc))
          (synCplc (Class.cv (nb068AlphaDummy141 f)) (synC1c))
          (Class.cv (nb068AlphaDummy141 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb068AlphaDummy132))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb068AlphaDummy134 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy146) from (by
                              unfold nb068AlphaDummy146;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0136) 1))))
                          (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy149 f) from (by
                              unfold nb068AlphaDummy149;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0137 f) 1))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy145) from (by
                                unfold nb068AlphaDummy145;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0136) 0))))
                            (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy148 f) from (by
                                unfold nb068AlphaDummy148;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0137 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy143) from (by
                                  unfold nb068AlphaDummy143;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0134) 0))))
                              (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy144 f) from
                                (by
                                  unfold nb068AlphaDummy144;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
                              (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.reflOfClosed
                            [((nb068AlphaDummy147), (nb068AlphaDummy150 f)),
                              ((nb068AlphaDummy146), (nb068AlphaDummy149 f)),
                              ((nb068AlphaDummy145), (nb068AlphaDummy148 f)),
                              ((nb068AlphaDummy143), (nb068AlphaDummy144 f)),
                              ((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
                              ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
                              ((nb068AlphaDummy165), (nb068AlphaDummy166 f)),
                              ((nb068AlphaDummy163), (nb068AlphaDummy164 f)),
                              ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
                              ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
                              ((nb068AlphaDummy161), (nb068AlphaDummy162 f)),
                              ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
                              ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                              ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                              ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                              ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                              ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                              ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                              ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                              ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                              ((nb068AlphaDummy001), x),
                              ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                            (synC1c) (by simp only [fv_syn_c1c])))
                        (TAlphaWff.neg (nb068SplitAlpha0182 x y f)))))))) (TAlphaWff.classMem
              (TAlphaClass.cv (TAlphaVar.there
                  (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy143) from (by
                      unfold nb068AlphaDummy143;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0134) 0))))
                  (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy144 f) from (by
                      unfold nb068AlphaDummy144;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                [((nb068AlphaDummy143), (nb068AlphaDummy144 f)),
                  ((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
                  ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
                  ((nb068AlphaDummy165), (nb068AlphaDummy166 f)),
                  ((nb068AlphaDummy163), (nb068AlphaDummy164 f)),
                  ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
                  ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
                  ((nb068AlphaDummy161), (nb068AlphaDummy162 f)),
                  ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
                  ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                  ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                  ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                  ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                  ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                  ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                  ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                  ((nb068AlphaDummy001), x),
                  ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy143) from (by
                    unfold nb068AlphaDummy143;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0134) 0))))
                (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy144 f) from (by
                    unfold nb068AlphaDummy144;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
                (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                (TAlphaVar.there (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy143) from
                    (by
                      unfold nb068AlphaDummy143;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0134) 0))))
                  (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy144 f) from (by
                      unfold nb068AlphaDummy144;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                [((nb068AlphaDummy143), (nb068AlphaDummy144 f)),
                  ((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
                  ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
                  ((nb068AlphaDummy165), (nb068AlphaDummy166 f)),
                  ((nb068AlphaDummy163), (nb068AlphaDummy164 f)),
                  ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
                  ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
                  ((nb068AlphaDummy161), (nb068AlphaDummy162 f)),
                  ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
                  ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                  ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                  ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                  ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                  ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                  ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                  ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                  ((nb068AlphaDummy001), x),
                  ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                (synCnnc) (by simp only [fv_syn_cnnc]))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part061`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0184`. -/
@[expose]
noncomputable def nb068SplitAlpha0184 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy161), (nb068AlphaDummy162 f)),
        ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
        ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy161))
          (Class.cab (nb068AlphaDummy131)
            (synWrex (nb068AlphaDummy132) (Class.cv (nb068AlphaDummy126))
              (Wff.classEq (Class.cv (nb068AlphaDummy131))
                (synCun (synCphi (Class.cv (nb068AlphaDummy132))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb068AlphaDummy161))
            (Class.cab (nb068AlphaDummy131)
              (synWrex (nb068AlphaDummy132) (Class.cv (nb068AlphaDummy126))
                (Wff.classEq (Class.cv (nb068AlphaDummy131))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy132)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy162 f))
          (Class.cab (nb068AlphaDummy133 f)
            (synWrex (nb068AlphaDummy134 f) (Class.cv (nb068AlphaDummy128 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy133 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy134 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb068AlphaDummy162 f))
            (Class.cab (nb068AlphaDummy133 f)
              (synWrex (nb068AlphaDummy134 f) (Class.cv (nb068AlphaDummy128 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy133 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy134 f)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy132) from
                    (by
                      unfold nb068AlphaDummy132;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0154) 1))))
                  (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy134 f) from (by
                      unfold nb068AlphaDummy134;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0156 f) 1))))
                  (TAlphaVar.there (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy131) from
                      (by
                        unfold nb068AlphaDummy131;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0154) 0))))
                    (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy133 f) from (by
                        unfold nb068AlphaDummy133;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0156 f) 0)))) (TAlphaVar.there
                      (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy161) from (by
                          unfold nb068AlphaDummy161;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0158) 0))))
                      (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy162 f) from (by
                          unfold nb068AlphaDummy162;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0159 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy135) from (by
                            unfold nb068AlphaDummy135;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0155) 0))))
                        (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy136 f) from (by
                            unfold nb068AlphaDummy136;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0157 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb068AlphaDummy125))).fv ∪
                      ((Class.cv (nb068AlphaDummy126))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb068AlphaDummy127 f))).fv ∪
                      ((Class.cv (nb068AlphaDummy128 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb068AlphaDummy132) ≠
        (nb068AlphaDummy139) from (by
          unfold nb068AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy141 f) from (by
          unfold nb068AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy140) from (by
          unfold nb068AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 1)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy142 f) from (by
          unfold nb068AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f) 1)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy165) from (by
          unfold nb068AlphaDummy165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0162) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy166 f) from (by
          unfold nb068AlphaDummy166;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0163 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy163) from (by
          unfold nb068AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0160) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy164 f) from (by
          unfold nb068AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0161 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068SplitAlpha0183 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb068AlphaDummy132) ≠
        (nb068AlphaDummy139) from (by
          unfold nb068AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy141 f) from (by
          unfold nb068AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy140) from (by
          unfold nb068AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 1)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy142 f) from (by
          unfold nb068AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f) 1)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy165) from (by
          unfold nb068AlphaDummy165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0162) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy166 f) from (by
          unfold nb068AlphaDummy166;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0163 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy163) from (by
          unfold nb068AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0160) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy164 f) from (by
          unfold nb068AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0161 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068SplitAlpha0183 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb068AlphaDummy163), (nb068AlphaDummy164 f)),
                          ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
                          ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
                          ((nb068AlphaDummy161), (nb068AlphaDummy162 f)),
                          ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
                          ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                          ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                          ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                          ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                          ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                          ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                          ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                          ((nb068AlphaDummy001), x),
                          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy132) from
                      (by
                        unfold nb068AlphaDummy132;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0154) 1))))
                    (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy134 f) from (by
                        unfold nb068AlphaDummy134;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0156 f) 1)))) (TAlphaVar.there
                      (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy131) from (by
                          unfold nb068AlphaDummy131;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0154) 0))))
                      (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy133 f) from (by
                          unfold nb068AlphaDummy133;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0156 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy161) from (by
                            unfold nb068AlphaDummy161;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0158) 0))))
                        (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy162 f) from (by
                            unfold nb068AlphaDummy162;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0159 f) 0))))
                        (TAlphaVar.there
                          (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy135) from (by
                              unfold nb068AlphaDummy135;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0155) 0))))
                          (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy136 f) from (by
                              unfold nb068AlphaDummy136;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0157 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb068AlphaDummy125))).fv ∪
                        ((Class.cv (nb068AlphaDummy126))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb068AlphaDummy127 f))).fv ∪
                        ((Class.cv (nb068AlphaDummy128 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy132) ≠ (nb068AlphaDummy139) from (by
          unfold nb068AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy141 f) from (by
          unfold nb068AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy140) from (by
          unfold nb068AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 1)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy142 f) from (by
          unfold nb068AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f) 1)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy165) from (by
          unfold nb068AlphaDummy165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0162) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy166 f) from (by
          unfold nb068AlphaDummy166;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0163 f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy132) ≠ (nb068AlphaDummy163)
        from (by
          unfold nb068AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0160)
                  0)))) (show (nb068AlphaDummy134 f) ≠ (nb068AlphaDummy164 f) from (by
          unfold nb068AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0161 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068SplitAlpha0183 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy132) ≠ (nb068AlphaDummy139) from (by
          unfold nb068AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy141 f) from (by
          unfold nb068AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy140) from (by
          unfold nb068AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 1)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy142 f) from (by
          unfold nb068AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f) 1)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy165) from (by
          unfold nb068AlphaDummy165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0162) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy166 f) from (by
          unfold nb068AlphaDummy166;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0163 f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy132) ≠ (nb068AlphaDummy163)
        from (by
          unfold nb068AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0160)
                  0)))) (show (nb068AlphaDummy134 f) ≠ (nb068AlphaDummy164 f) from (by
          unfold nb068AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0161 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068SplitAlpha0183 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb068AlphaDummy163), (nb068AlphaDummy164 f)),
                            ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
                            ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
                            ((nb068AlphaDummy161), (nb068AlphaDummy162 f)),
                            ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
                            ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                            ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                            ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                            ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                            ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                            ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                            ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                            ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                            ((nb068AlphaDummy001), x),
                            ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0185`. -/
@[expose]
noncomputable def nb068SplitAlpha0185 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy183), (nb068AlphaDummy186 f)),
        ((nb068AlphaDummy182), (nb068AlphaDummy185 f)),
        ((nb068AlphaDummy181), (nb068AlphaDummy184 f)),
        ((nb068AlphaDummy179), (nb068AlphaDummy180 f)),
        ((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
        ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
        ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
        ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
        ((nb068AlphaDummy173), (nb068AlphaDummy174 f)),
        ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
        ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb068AlphaDummy182)) (Class.cv (nb068AlphaDummy183)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb068AlphaDummy181))
            (synCun (Class.cv (nb068AlphaDummy182)) (Class.cv (nb068AlphaDummy183))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb068AlphaDummy185 f))
            (Class.cv (nb068AlphaDummy186 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy184 f))
            (synCun (Class.cv (nb068AlphaDummy185 f))
              (Class.cv (nb068AlphaDummy186 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy189) from (by
                              unfold nb068AlphaDummy189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0178) 0))))
                          (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy190 f) from (by
                              unfold nb068AlphaDummy190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0179 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy187) from (by
                                unfold nb068AlphaDummy187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0176) 0))))
                            (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy188 f) from (by
                                unfold nb068AlphaDummy188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0177 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy189) from (by
                              unfold nb068AlphaDummy189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0182) 0))))
                          (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy190 f) from (by
                              unfold nb068AlphaDummy190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0183 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy187) from (by
                                unfold nb068AlphaDummy187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0180) 0))))
                            (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy188 f) from (by
                                unfold nb068AlphaDummy188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0181 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy189) from (by
                              unfold nb068AlphaDummy189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0178) 0))))
                          (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy190 f) from (by
                              unfold nb068AlphaDummy190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0179 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy187) from (by
                                unfold nb068AlphaDummy187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0176) 0))))
                            (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy188 f) from (by
                                unfold nb068AlphaDummy188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0177 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy189) from (by
                              unfold nb068AlphaDummy189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0182) 0))))
                          (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy190 f) from (by
                              unfold nb068AlphaDummy190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0183 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy187) from (by
                                unfold nb068AlphaDummy187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0180) 0))))
                            (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy188 f) from (by
                                unfold nb068AlphaDummy188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0181 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb068AlphaDummy183), (nb068AlphaDummy186 f)),
          ((nb068AlphaDummy182), (nb068AlphaDummy185 f)),
          ((nb068AlphaDummy181), (nb068AlphaDummy184 f)),
          ((nb068AlphaDummy179), (nb068AlphaDummy180 f)),
          ((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
          ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
          ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
          ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
          ((nb068AlphaDummy173), (nb068AlphaDummy174 f)),
          ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
          ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
          ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
          ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
          ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
          ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
          ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
          ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
          ((nb068AlphaDummy001), x),
          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy193) from (by
                                unfold nb068AlphaDummy193;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0186) 0))))
                            (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy194 f) from (by
                                unfold nb068AlphaDummy194;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0187 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy191) from (by
                                  unfold nb068AlphaDummy191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0184) 0))))
                              (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy192 f) from
                                (by
                                  unfold nb068AlphaDummy192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0185 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy193) from (by
                                unfold nb068AlphaDummy193;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0186) 0))))
                            (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy194 f) from (by
                                unfold nb068AlphaDummy194;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0187 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy191) from (by
                                  unfold nb068AlphaDummy191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0184) 0))))
                              (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy192 f) from
                                (by
                                  unfold nb068AlphaDummy192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0185 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy195) from (by
                                unfold nb068AlphaDummy195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0190) 0))))
                            (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy196 f) from (by
                                unfold nb068AlphaDummy196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0191 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy191) from (by
                                  unfold nb068AlphaDummy191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0188) 0))))
                              (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy192 f) from
                                (by
                                  unfold nb068AlphaDummy192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0189 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy195) from (by
                                unfold nb068AlphaDummy195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0190) 0))))
                            (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy196 f) from (by
                                unfold nb068AlphaDummy196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0191 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy191) from (by
                                  unfold nb068AlphaDummy191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0188) 0))))
                              (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy192 f) from
                                (by
                                  unfold nb068AlphaDummy192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0189 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0186`. -/
@[expose]
noncomputable def nb068SplitAlpha0186 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
        ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
        ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
        ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
        ((nb068AlphaDummy173), (nb068AlphaDummy174 f)),
        ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
        ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy175))
          (Class.cv (nb068AlphaDummy168))) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy176))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy175)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy175)) (synC1c))
              (Class.cv (nb068AlphaDummy175))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy177 f))
          (Class.cv (nb068AlphaDummy170 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy178 f))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy177 f)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy177 f)) (synC1c))
              (Class.cv (nb068AlphaDummy177 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy168) ≠ (nb068AlphaDummy175) from (by
              unfold nb068AlphaDummy175;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0170) 0))))
          (show (nb068AlphaDummy170 f) ≠ (nb068AlphaDummy177 f) from (by
              unfold nb068AlphaDummy177;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0171 f) 0))))
          (TAlphaVar.there (show (nb068AlphaDummy168) ≠ (nb068AlphaDummy176) from (by
                unfold nb068AlphaDummy176;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0170) 1))))
            (show (nb068AlphaDummy170 f) ≠ (nb068AlphaDummy178 f) from (by
                unfold nb068AlphaDummy178;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0171 f) 1))))
            (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy168))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb068AlphaDummy170 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy182) from (by
                                  unfold nb068AlphaDummy182;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0174) 1))))
                              (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy185 f) from
                                (by
                                  unfold nb068AlphaDummy185;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0175 f) 1))))
                              (TAlphaVar.there
                                (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy181) from (by
                                    unfold nb068AlphaDummy181;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0174) 0)))) (show
                                  (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy184 f) from (by
                                    unfold nb068AlphaDummy184;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0175 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy179) from
                                    (by
                                      unfold nb068AlphaDummy179;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0172)
                                              0)))) (show
                                    (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy180 f) from
                                    (by
                                      unfold nb068AlphaDummy180;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0173 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb068AlphaDummy183), (nb068AlphaDummy186 f)),
                                  ((nb068AlphaDummy182), (nb068AlphaDummy185 f)),
                                  ((nb068AlphaDummy181), (nb068AlphaDummy184 f)),
                                  ((nb068AlphaDummy179), (nb068AlphaDummy180 f)),
                                  ((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
                                  ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
                                  ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
                                  ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
                                  ((nb068AlphaDummy173), (nb068AlphaDummy174 f)),
                                  ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
                                  ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                                  ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                                  ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                                  ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                                  ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                                  ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                                  ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                                  ((nb068AlphaDummy001), x), ((nb068AlphaDummy003),
                                    (nb068AlphaDummy004 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb068SplitAlpha0185 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy179) from (by
                          unfold nb068AlphaDummy179;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0172) 0))))
                      (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy180 f) from (by
                          unfold nb068AlphaDummy180;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb068AlphaDummy179), (nb068AlphaDummy180 f)),
                      ((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
                      ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
                      ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
                      ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
                      ((nb068AlphaDummy173), (nb068AlphaDummy174 f)),
                      ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
                      ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                      ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                      ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                      ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                      ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                      ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                      ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                      ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                      ((nb068AlphaDummy001), x),
                      ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy179) from
                      (by
                        unfold nb068AlphaDummy179;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0172) 0))))
                    (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy180 f) from (by
                        unfold nb068AlphaDummy180;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy179) from (by
                          unfold nb068AlphaDummy179;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0172) 0))))
                      (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy180 f) from (by
                          unfold nb068AlphaDummy180;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb068AlphaDummy179), (nb068AlphaDummy180 f)),
                      ((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
                      ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
                      ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
                      ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
                      ((nb068AlphaDummy173), (nb068AlphaDummy174 f)),
                      ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
                      ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                      ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                      ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                      ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                      ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                      ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                      ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                      ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                      ((nb068AlphaDummy001), x),
                      ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part062`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0187`. -/
@[expose]
noncomputable def nb068SplitAlpha0187 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy183), (nb068AlphaDummy186 f)),
        ((nb068AlphaDummy182), (nb068AlphaDummy185 f)),
        ((nb068AlphaDummy181), (nb068AlphaDummy184 f)),
        ((nb068AlphaDummy179), (nb068AlphaDummy180 f)),
        ((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
        ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
        ((nb068AlphaDummy201), (nb068AlphaDummy202 f)),
        ((nb068AlphaDummy199), (nb068AlphaDummy200 f)),
        ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
        ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
        ((nb068AlphaDummy197), (nb068AlphaDummy198 f)),
        ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
        ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb068AlphaDummy182)) (Class.cv (nb068AlphaDummy183)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb068AlphaDummy181))
            (synCun (Class.cv (nb068AlphaDummy182)) (Class.cv (nb068AlphaDummy183))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb068AlphaDummy185 f))
            (Class.cv (nb068AlphaDummy186 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy184 f))
            (synCun (Class.cv (nb068AlphaDummy185 f))
              (Class.cv (nb068AlphaDummy186 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy189) from (by
                              unfold nb068AlphaDummy189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0178) 0))))
                          (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy190 f) from (by
                              unfold nb068AlphaDummy190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0179 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy187) from (by
                                unfold nb068AlphaDummy187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0176) 0))))
                            (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy188 f) from (by
                                unfold nb068AlphaDummy188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0177 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy189) from (by
                              unfold nb068AlphaDummy189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0182) 0))))
                          (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy190 f) from (by
                              unfold nb068AlphaDummy190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0183 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy187) from (by
                                unfold nb068AlphaDummy187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0180) 0))))
                            (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy188 f) from (by
                                unfold nb068AlphaDummy188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0181 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy189) from (by
                              unfold nb068AlphaDummy189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0178) 0))))
                          (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy190 f) from (by
                              unfold nb068AlphaDummy190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0179 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy187) from (by
                                unfold nb068AlphaDummy187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0176) 0))))
                            (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy188 f) from (by
                                unfold nb068AlphaDummy188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0177 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy189) from (by
                              unfold nb068AlphaDummy189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0182) 0))))
                          (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy190 f) from (by
                              unfold nb068AlphaDummy190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0183 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy187) from (by
                                unfold nb068AlphaDummy187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0180) 0))))
                            (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy188 f) from (by
                                unfold nb068AlphaDummy188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0181 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb068AlphaDummy183), (nb068AlphaDummy186 f)),
          ((nb068AlphaDummy182), (nb068AlphaDummy185 f)),
          ((nb068AlphaDummy181), (nb068AlphaDummy184 f)),
          ((nb068AlphaDummy179), (nb068AlphaDummy180 f)),
          ((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
          ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
          ((nb068AlphaDummy201), (nb068AlphaDummy202 f)),
          ((nb068AlphaDummy199), (nb068AlphaDummy200 f)),
          ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
          ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
          ((nb068AlphaDummy197), (nb068AlphaDummy198 f)),
          ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
          ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
          ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
          ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
          ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
          ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
          ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
          ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
          ((nb068AlphaDummy001), x),
          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy193) from (by
                                unfold nb068AlphaDummy193;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0186) 0))))
                            (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy194 f) from (by
                                unfold nb068AlphaDummy194;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0187 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy191) from (by
                                  unfold nb068AlphaDummy191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0184) 0))))
                              (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy192 f) from
                                (by
                                  unfold nb068AlphaDummy192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0185 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy193) from (by
                                unfold nb068AlphaDummy193;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0186) 0))))
                            (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy194 f) from (by
                                unfold nb068AlphaDummy194;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0187 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy191) from (by
                                  unfold nb068AlphaDummy191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0184) 0))))
                              (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy192 f) from
                                (by
                                  unfold nb068AlphaDummy192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0185 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy195) from (by
                                unfold nb068AlphaDummy195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0190) 0))))
                            (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy196 f) from (by
                                unfold nb068AlphaDummy196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0191 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy191) from (by
                                  unfold nb068AlphaDummy191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0188) 0))))
                              (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy192 f) from
                                (by
                                  unfold nb068AlphaDummy192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0189 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy195) from (by
                                unfold nb068AlphaDummy195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0190) 0))))
                            (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy196 f) from (by
                                unfold nb068AlphaDummy196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0191 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy191) from (by
                                  unfold nb068AlphaDummy191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0188) 0))))
                              (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy192 f) from
                                (by
                                  unfold nb068AlphaDummy192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0189 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0188`. -/
@[expose]
noncomputable def nb068SplitAlpha0188 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
        ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
        ((nb068AlphaDummy201), (nb068AlphaDummy202 f)),
        ((nb068AlphaDummy199), (nb068AlphaDummy200 f)),
        ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
        ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
        ((nb068AlphaDummy197), (nb068AlphaDummy198 f)),
        ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
        ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.classEq (Class.cv (nb068AlphaDummy176))
        (synCif (Wff.classMem (Class.cv (nb068AlphaDummy175)) (synCnnc))
          (synCplc (Class.cv (nb068AlphaDummy175)) (synC1c))
          (Class.cv (nb068AlphaDummy175))))
      (Wff.classEq (Class.cv (nb068AlphaDummy178 f))
        (synCif (Wff.classMem (Class.cv (nb068AlphaDummy177 f)) (synCnnc))
          (synCplc (Class.cv (nb068AlphaDummy177 f)) (synC1c))
          (Class.cv (nb068AlphaDummy177 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb068AlphaDummy168))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb068AlphaDummy170 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy182) from (by
                              unfold nb068AlphaDummy182;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0174) 1))))
                          (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy185 f) from (by
                              unfold nb068AlphaDummy185;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0175 f) 1))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy181) from (by
                                unfold nb068AlphaDummy181;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0174) 0))))
                            (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy184 f) from (by
                                unfold nb068AlphaDummy184;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0175 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy179) from (by
                                  unfold nb068AlphaDummy179;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0172) 0))))
                              (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy180 f) from
                                (by
                                  unfold nb068AlphaDummy180;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
                              (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.reflOfClosed
                            [((nb068AlphaDummy183), (nb068AlphaDummy186 f)),
                              ((nb068AlphaDummy182), (nb068AlphaDummy185 f)),
                              ((nb068AlphaDummy181), (nb068AlphaDummy184 f)),
                              ((nb068AlphaDummy179), (nb068AlphaDummy180 f)),
                              ((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
                              ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
                              ((nb068AlphaDummy201), (nb068AlphaDummy202 f)),
                              ((nb068AlphaDummy199), (nb068AlphaDummy200 f)),
                              ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
                              ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
                              ((nb068AlphaDummy197), (nb068AlphaDummy198 f)),
                              ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
                              ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                              ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                              ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                              ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                              ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                              ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                              ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                              ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                              ((nb068AlphaDummy001), x),
                              ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                            (synC1c) (by simp only [fv_syn_c1c])))
                        (TAlphaWff.neg (nb068SplitAlpha0187 x y f)))))))) (TAlphaWff.classMem
              (TAlphaClass.cv (TAlphaVar.there
                  (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy179) from (by
                      unfold nb068AlphaDummy179;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0172) 0))))
                  (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy180 f) from (by
                      unfold nb068AlphaDummy180;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                [((nb068AlphaDummy179), (nb068AlphaDummy180 f)),
                  ((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
                  ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
                  ((nb068AlphaDummy201), (nb068AlphaDummy202 f)),
                  ((nb068AlphaDummy199), (nb068AlphaDummy200 f)),
                  ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
                  ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
                  ((nb068AlphaDummy197), (nb068AlphaDummy198 f)),
                  ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
                  ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                  ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                  ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                  ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                  ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                  ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                  ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                  ((nb068AlphaDummy001), x),
                  ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy179) from (by
                    unfold nb068AlphaDummy179;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0172) 0))))
                (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy180 f) from (by
                    unfold nb068AlphaDummy180;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
                (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                (TAlphaVar.there (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy179) from
                    (by
                      unfold nb068AlphaDummy179;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0172) 0))))
                  (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy180 f) from (by
                      unfold nb068AlphaDummy180;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                [((nb068AlphaDummy179), (nb068AlphaDummy180 f)),
                  ((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
                  ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
                  ((nb068AlphaDummy201), (nb068AlphaDummy202 f)),
                  ((nb068AlphaDummy199), (nb068AlphaDummy200 f)),
                  ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
                  ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
                  ((nb068AlphaDummy197), (nb068AlphaDummy198 f)),
                  ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
                  ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                  ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                  ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                  ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                  ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                  ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                  ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                  ((nb068AlphaDummy001), x),
                  ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                (synCnnc) (by simp only [fv_syn_cnnc]))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0189`. -/
@[expose]
noncomputable def nb068SplitAlpha0189 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy197), (nb068AlphaDummy198 f)),
        ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
        ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy197))
          (Class.cab (nb068AlphaDummy167)
            (synWrex (nb068AlphaDummy168) (Class.cv (nb068AlphaDummy125))
              (Wff.classEq (Class.cv (nb068AlphaDummy167))
                (synCun (synCphi (Class.cv (nb068AlphaDummy168))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb068AlphaDummy197))
            (Class.cab (nb068AlphaDummy167)
              (synWrex (nb068AlphaDummy168) (Class.cv (nb068AlphaDummy125))
                (Wff.classEq (Class.cv (nb068AlphaDummy167))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy168)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy198 f))
          (Class.cab (nb068AlphaDummy169 f)
            (synWrex (nb068AlphaDummy170 f) (Class.cv (nb068AlphaDummy127 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy169 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy170 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb068AlphaDummy198 f))
            (Class.cab (nb068AlphaDummy169 f)
              (synWrex (nb068AlphaDummy170 f) (Class.cv (nb068AlphaDummy127 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy169 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy170 f)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy168) from
                    (by
                      unfold nb068AlphaDummy168;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0192) 1))))
                  (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy170 f) from (by
                      unfold nb068AlphaDummy170;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0194 f) 1))))
                  (TAlphaVar.there (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy167) from
                      (by
                        unfold nb068AlphaDummy167;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0192) 0))))
                    (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy169 f) from (by
                        unfold nb068AlphaDummy169;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0194 f) 0)))) (TAlphaVar.there
                      (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy197) from (by
                          unfold nb068AlphaDummy197;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0196) 0))))
                      (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy198 f) from (by
                          unfold nb068AlphaDummy198;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0197 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy171) from (by
                            unfold nb068AlphaDummy171;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0193) 0))))
                        (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy172 f) from (by
                            unfold nb068AlphaDummy172;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0195 f) 0))))
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb068AlphaDummy000))).fv)
                            (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb068AlphaDummy126))).fv ∪
                      ((Class.cv (nb068AlphaDummy125))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb068AlphaDummy128 f))).fv ∪
                      ((Class.cv (nb068AlphaDummy127 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb068AlphaDummy168) ≠
        (nb068AlphaDummy175) from (by
          unfold nb068AlphaDummy175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0170) 0)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy177 f) from (by
          unfold nb068AlphaDummy177;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0171 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy168) ≠ (nb068AlphaDummy176) from (by
          unfold nb068AlphaDummy176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0170) 1)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy178 f) from (by
          unfold nb068AlphaDummy178;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0171 f) 1)))) (TAlphaVar.there (show
        (nb068AlphaDummy168) ≠ (nb068AlphaDummy201) from (by
          unfold nb068AlphaDummy201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0200) 0)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy202 f) from (by
          unfold nb068AlphaDummy202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0201 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy168) ≠ (nb068AlphaDummy199) from (by
          unfold nb068AlphaDummy199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0198) 0)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy200 f) from (by
          unfold nb068AlphaDummy200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0199 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068SplitAlpha0188 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb068AlphaDummy168) ≠
        (nb068AlphaDummy175) from (by
          unfold nb068AlphaDummy175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0170) 0)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy177 f) from (by
          unfold nb068AlphaDummy177;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0171 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy168) ≠ (nb068AlphaDummy176) from (by
          unfold nb068AlphaDummy176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0170) 1)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy178 f) from (by
          unfold nb068AlphaDummy178;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0171 f) 1)))) (TAlphaVar.there (show
        (nb068AlphaDummy168) ≠ (nb068AlphaDummy201) from (by
          unfold nb068AlphaDummy201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0200) 0)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy202 f) from (by
          unfold nb068AlphaDummy202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0201 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy168) ≠ (nb068AlphaDummy199) from (by
          unfold nb068AlphaDummy199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0198) 0)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy200 f) from (by
          unfold nb068AlphaDummy200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0199 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068SplitAlpha0188 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb068AlphaDummy199), (nb068AlphaDummy200 f)),
                          ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
                          ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
                          ((nb068AlphaDummy197), (nb068AlphaDummy198 f)),
                          ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
                          ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                          ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                          ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                          ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                          ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                          ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                          ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                          ((nb068AlphaDummy001), x),
                          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy168) from
                      (by
                        unfold nb068AlphaDummy168;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0192) 1))))
                    (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy170 f) from (by
                        unfold nb068AlphaDummy170;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0194 f) 1)))) (TAlphaVar.there
                      (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy167) from (by
                          unfold nb068AlphaDummy167;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0192) 0))))
                      (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy169 f) from (by
                          unfold nb068AlphaDummy169;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0194 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy197) from (by
                            unfold nb068AlphaDummy197;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0196) 0))))
                        (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy198 f) from (by
                            unfold nb068AlphaDummy198;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0197 f) 0))))
                        (TAlphaVar.there
                          (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy171) from (by
                              unfold nb068AlphaDummy171;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0193) 0))))
                          (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy172 f) from (by
                              unfold nb068AlphaDummy172;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0195 f) 0))))
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb068AlphaDummy000))).fv)
                              (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb068AlphaDummy126))).fv ∪
                        ((Class.cv (nb068AlphaDummy125))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb068AlphaDummy128 f))).fv ∪
                        ((Class.cv (nb068AlphaDummy127 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy168) ≠ (nb068AlphaDummy175) from (by
          unfold nb068AlphaDummy175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0170) 0)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy177 f) from (by
          unfold nb068AlphaDummy177;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0171 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy168) ≠ (nb068AlphaDummy176) from (by
          unfold nb068AlphaDummy176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0170) 1)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy178 f) from (by
          unfold nb068AlphaDummy178;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0171 f) 1)))) (TAlphaVar.there (show
        (nb068AlphaDummy168) ≠ (nb068AlphaDummy201) from (by
          unfold nb068AlphaDummy201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0200) 0)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy202 f) from (by
          unfold nb068AlphaDummy202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0201 f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy168) ≠ (nb068AlphaDummy199)
        from (by
          unfold nb068AlphaDummy199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0198)
                  0)))) (show (nb068AlphaDummy170 f) ≠ (nb068AlphaDummy200 f) from (by
          unfold nb068AlphaDummy200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0199 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068SplitAlpha0188 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy168) ≠ (nb068AlphaDummy175) from (by
          unfold nb068AlphaDummy175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0170) 0)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy177 f) from (by
          unfold nb068AlphaDummy177;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0171 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy168) ≠ (nb068AlphaDummy176) from (by
          unfold nb068AlphaDummy176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0170) 1)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy178 f) from (by
          unfold nb068AlphaDummy178;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0171 f) 1)))) (TAlphaVar.there (show
        (nb068AlphaDummy168) ≠ (nb068AlphaDummy201) from (by
          unfold nb068AlphaDummy201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0200) 0)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy202 f) from (by
          unfold nb068AlphaDummy202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0201 f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy168) ≠ (nb068AlphaDummy199)
        from (by
          unfold nb068AlphaDummy199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0198)
                  0)))) (show (nb068AlphaDummy170 f) ≠ (nb068AlphaDummy200 f) from (by
          unfold nb068AlphaDummy200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0199 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068SplitAlpha0188 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb068AlphaDummy199), (nb068AlphaDummy200 f)),
                            ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
                            ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
                            ((nb068AlphaDummy197), (nb068AlphaDummy198 f)),
                            ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
                            ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                            ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                            ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                            ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                            ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                            ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                            ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                            ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                            ((nb068AlphaDummy001), x),
                            ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0190`. -/
@[expose]
noncomputable def nb068SplitAlpha0190 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classEq (Class.cv (nb068AlphaDummy129))
          (synCop (Class.cv (nb068AlphaDummy125)) (Class.cv (nb068AlphaDummy126))))
        (Wff.neg (synWbr (Class.cv (nb068AlphaDummy126)) (Class.cv (nb068AlphaDummy000))
            (Class.cv (nb068AlphaDummy125)))))
      (Wff.imp (Wff.classEq (Class.cv (nb068AlphaDummy130 f))
          (synCop (Class.cv (nb068AlphaDummy127 f)) (Class.cv (nb068AlphaDummy128 f))))
        (Wff.neg (synWbr (Class.cv (nb068AlphaDummy128 f)) (Class.cv f)
            (Class.cv (nb068AlphaDummy127 f))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
            (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy129) from (by
                unfold nb068AlphaDummy129;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0124) 0))))) (Ne.symm
            (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy130 f) from (by
                unfold nb068AlphaDummy130;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0125 f) 0)))))
          (TAlphaVar.there (Ne.symm (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy129) from
                (by
                  unfold nb068AlphaDummy129;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0122) 0)))))
            (Ne.symm (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy130 f) from (by
                  unfold nb068AlphaDummy130;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0123 f) 0)))))
            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy132) from
                                    (by
                                      unfold nb068AlphaDummy132;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0126)
                                              1)))) (show
                                    (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy134 f) from
                                    (by
                                      unfold nb068AlphaDummy134;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0128 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb068AlphaDummy125) ≠ (nb068AlphaDummy131) from (by
                                        unfold nb068AlphaDummy131;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0126)
                                                0)))) (show (nb068AlphaDummy127 f) ≠
                                        (nb068AlphaDummy133 f) from (by
                                        unfold nb068AlphaDummy133;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0128 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy125) ≠ (nb068AlphaDummy137) from
                                        (by
                                          unfold nb068AlphaDummy137;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0130)
                                                  0)))) (show (nb068AlphaDummy127 f) ≠
        (nb068AlphaDummy138 f) from (by
                                          unfold nb068AlphaDummy138;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0131 f) 0))))
                                      (TAlphaVar.there (show (nb068AlphaDummy125) ≠
        (nb068AlphaDummy135) from (by
          unfold nb068AlphaDummy135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0127) 0)))) (show (nb068AlphaDummy127 f) ≠
        (nb068AlphaDummy136 f) from (by
          unfold nb068AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0129 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb068AlphaDummy000))).fv) (by decide))
        (freshVar_injective (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb068AlphaDummy125))).fv ∪
                                      ((Class.cv (nb068AlphaDummy126))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb068AlphaDummy127 f))).fv ∪
                                      ((Class.cv (nb068AlphaDummy128 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068SplitAlpha0181 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy132) from
                                    (by
                                      unfold nb068AlphaDummy132;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0126)
                                              1)))) (show
                                    (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy134 f) from
                                    (by
                                      unfold nb068AlphaDummy134;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0128 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb068AlphaDummy125) ≠ (nb068AlphaDummy131) from (by
                                        unfold nb068AlphaDummy131;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0126)
                                                0)))) (show (nb068AlphaDummy127 f) ≠
                                        (nb068AlphaDummy133 f) from (by
                                        unfold nb068AlphaDummy133;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0128 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy125) ≠ (nb068AlphaDummy137) from
                                        (by
                                          unfold nb068AlphaDummy137;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0130)
                                                  0)))) (show (nb068AlphaDummy127 f) ≠
        (nb068AlphaDummy138 f) from (by
                                          unfold nb068AlphaDummy138;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0131 f) 0))))
                                      (TAlphaVar.there (show (nb068AlphaDummy125) ≠
        (nb068AlphaDummy135) from (by
          unfold nb068AlphaDummy135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0127) 0)))) (show (nb068AlphaDummy127 f) ≠
        (nb068AlphaDummy136 f) from (by
          unfold nb068AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0129 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb068AlphaDummy000))).fv) (by decide))
        (freshVar_injective (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb068AlphaDummy125))).fv ∪
                                      ((Class.cv (nb068AlphaDummy126))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb068AlphaDummy127 f))).fv ∪
                                      ((Class.cv (nb068AlphaDummy128 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068SplitAlpha0181 x y f)))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb068SplitAlpha0184 x y f)))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb068AlphaDummy126) ≠ (nb068AlphaDummy168) from (by
                                        unfold nb068AlphaDummy168;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0164)
                                                1)))) (show (nb068AlphaDummy128 f) ≠
                                        (nb068AlphaDummy170 f) from (by
                                        unfold nb068AlphaDummy170;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0166 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy126) ≠ (nb068AlphaDummy167) from
                                        (by
                                          unfold nb068AlphaDummy167;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0164)
                                                  0)))) (show (nb068AlphaDummy128 f) ≠
        (nb068AlphaDummy169 f) from (by
                                          unfold nb068AlphaDummy169;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0166 f) 0))))
                                      (TAlphaVar.there (show (nb068AlphaDummy126) ≠
        (nb068AlphaDummy173) from (by
          unfold nb068AlphaDummy173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0168) 0)))) (show (nb068AlphaDummy128 f) ≠
        (nb068AlphaDummy174 f) from (by
          unfold nb068AlphaDummy174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0169 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy126) ≠ (nb068AlphaDummy171) from (by
          unfold nb068AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0165) 0)))) (show (nb068AlphaDummy128 f) ≠
        (nb068AlphaDummy172 f) from (by
          unfold nb068AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0167 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb068AlphaDummy126))).fv ∪
                                        ((Class.cv (nb068AlphaDummy125))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb068AlphaDummy128 f))).fv ∪
                                        ((Class.cv (nb068AlphaDummy127 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068SplitAlpha0186 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb068AlphaDummy126) ≠ (nb068AlphaDummy168) from (by
                                        unfold nb068AlphaDummy168;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0164)
                                                1)))) (show (nb068AlphaDummy128 f) ≠
                                        (nb068AlphaDummy170 f) from (by
                                        unfold nb068AlphaDummy170;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0166 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy126) ≠ (nb068AlphaDummy167) from
                                        (by
                                          unfold nb068AlphaDummy167;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0164)
                                                  0)))) (show (nb068AlphaDummy128 f) ≠
        (nb068AlphaDummy169 f) from (by
                                          unfold nb068AlphaDummy169;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0166 f) 0))))
                                      (TAlphaVar.there (show (nb068AlphaDummy126) ≠
        (nb068AlphaDummy173) from (by
          unfold nb068AlphaDummy173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0168) 0)))) (show (nb068AlphaDummy128 f) ≠
        (nb068AlphaDummy174 f) from (by
          unfold nb068AlphaDummy174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0169 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy126) ≠ (nb068AlphaDummy171) from (by
          unfold nb068AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0165) 0)))) (show (nb068AlphaDummy128 f) ≠
        (nb068AlphaDummy172 f) from (by
          unfold nb068AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0167 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb068AlphaDummy126))).fv ∪
                                        ((Class.cv (nb068AlphaDummy125))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb068AlphaDummy128 f))).fv ∪
                                        ((Class.cv (nb068AlphaDummy127 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068SplitAlpha0186 x y f)))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb068SplitAlpha0189 x y f))))))))
        (TAlphaClass.cv (TAlphaVar.there
            (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy126) from (by
                unfold nb068AlphaDummy126;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0212) 1))))
            (show f ≠ (nb068AlphaDummy128 f) from (by
                unfold nb068AlphaDummy128;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0213 f) 1))))
            (TAlphaVar.there (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy125) from (by
                  unfold nb068AlphaDummy125;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0212) 0))))
              (show f ≠ (nb068AlphaDummy127 f) from (by
                  unfold nb068AlphaDummy127;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0213 f) 0))))
              (TAlphaVar.there (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy129) from (by
                    unfold nb068AlphaDummy129;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0210) 0))))
                (show f ≠ (nb068AlphaDummy130 f) from (by
                    unfold nb068AlphaDummy130;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0211 f) 0))))
                (TAlphaVar.there (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy329) from
                    (by
                      unfold nb068AlphaDummy329;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0504) 2))))
                  (show f ≠ (nb068AlphaDummy332 f) from (by
                      unfold nb068AlphaDummy332;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0506 f) 2))))
                  (TAlphaVar.there (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy328) from
                      (by
                        unfold nb068AlphaDummy328;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0504) 1))))
                    (show f ≠ (nb068AlphaDummy331 f) from (by
                        unfold nb068AlphaDummy331;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0506 f) 1)))) (TAlphaVar.there
                      (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy327) from (by
                          unfold nb068AlphaDummy327;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0504) 0))))
                      (show f ≠ (nb068AlphaDummy330 f) from (by
                          unfold nb068AlphaDummy330;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0506 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy333) from (by
                            unfold nb068AlphaDummy333;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0505) 0))))
                        (show f ≠ (nb068AlphaDummy334 f) from (by
                            unfold nb068AlphaDummy334;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0507 f) 0))))
                        (TAlphaVar.here _ _ _))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0191`. -/
@[expose]
noncomputable def nb068SplitAlpha0191 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (synWbr (Class.cv (nb068AlphaDummy327))
          (synCcnv (synCcnv (Class.cv (nb068AlphaDummy000))))
          (Class.cv (nb068AlphaDummy329))) (Wff.neg
          (synWbr (Class.cv (nb068AlphaDummy329))
            (synCcnv (Class.cv (nb068AlphaDummy000))) (Class.cv (nb068AlphaDummy328)))))
      (Wff.imp (synWbr (Class.cv (nb068AlphaDummy330 f)) (synCcnv (synCcnv (Class.cv f)))
          (Class.cv (nb068AlphaDummy332 f))) (Wff.neg
          (synWbr (Class.cv (nb068AlphaDummy332 f)) (synCcnv (Class.cv f))
            (Class.cv (nb068AlphaDummy331 f))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb068AlphaDummy327) ≠ (nb068AlphaDummy372) from
                                    (by
                                      unfold nb068AlphaDummy372;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0382)
                                              1)))) (show
                                    (nb068AlphaDummy330 f) ≠ (nb068AlphaDummy374 f) from
                                    (by
                                      unfold nb068AlphaDummy374;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0384 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb068AlphaDummy327) ≠ (nb068AlphaDummy371) from (by
                                        unfold nb068AlphaDummy371;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0382)
                                                0)))) (show (nb068AlphaDummy330 f) ≠
                                        (nb068AlphaDummy373 f) from (by
                                        unfold nb068AlphaDummy373;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0384 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy327) ≠ (nb068AlphaDummy377) from
                                        (by
                                          unfold nb068AlphaDummy377;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0386)
                                                  0)))) (show (nb068AlphaDummy330 f) ≠
        (nb068AlphaDummy378 f) from (by
                                          unfold nb068AlphaDummy378;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0387 f) 0))))
                                      (TAlphaVar.there (show (nb068AlphaDummy327) ≠
        (nb068AlphaDummy375) from (by
          unfold nb068AlphaDummy375;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0383) 0)))) (show (nb068AlphaDummy330 f) ≠
        (nb068AlphaDummy376 f) from (by
          unfold nb068AlphaDummy376;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0385 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((synCcnv (Class.cv (nb068AlphaDummy000)))).fv ∪ ((synCcnv (synCcnv (Class.cv
        (nb068AlphaDummy000))))).fv) (by decide)) (freshVar_injective
        (((synCcnv (Class.cv f))).fv ∪ ((synCcnv (synCcnv (Class.cv f)))).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((synCcnv (Class.cv
        (nb068AlphaDummy000)))).fv ∪ ((synCcnv (synCcnv (Class.cv
        (nb068AlphaDummy000))))).fv) (by decide)) (freshVar_injective
        (((synCcnv (Class.cv f))).fv ∪ ((synCcnv (synCcnv (Class.cv f)))).fv) (by decide))
        (TAlphaVar.here _ _ _))))))))) (nb068SplitAlpha0148 x y f)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb068AlphaDummy327) ≠ (nb068AlphaDummy372) from
                                    (by
                                      unfold nb068AlphaDummy372;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0382)
                                              1)))) (show
                                    (nb068AlphaDummy330 f) ≠ (nb068AlphaDummy374 f) from
                                    (by
                                      unfold nb068AlphaDummy374;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0384 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb068AlphaDummy327) ≠ (nb068AlphaDummy371) from (by
                                        unfold nb068AlphaDummy371;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0382)
                                                0)))) (show (nb068AlphaDummy330 f) ≠
                                        (nb068AlphaDummy373 f) from (by
                                        unfold nb068AlphaDummy373;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0384 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy327) ≠ (nb068AlphaDummy377) from
                                        (by
                                          unfold nb068AlphaDummy377;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0386)
                                                  0)))) (show (nb068AlphaDummy330 f) ≠
        (nb068AlphaDummy378 f) from (by
                                          unfold nb068AlphaDummy378;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0387 f) 0))))
                                      (TAlphaVar.there (show (nb068AlphaDummy327) ≠
        (nb068AlphaDummy375) from (by
          unfold nb068AlphaDummy375;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0383) 0)))) (show (nb068AlphaDummy330 f) ≠
        (nb068AlphaDummy376 f) from (by
          unfold nb068AlphaDummy376;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0385 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((synCcnv (Class.cv (nb068AlphaDummy000)))).fv ∪ ((synCcnv (synCcnv (Class.cv
        (nb068AlphaDummy000))))).fv) (by decide)) (freshVar_injective
        (((synCcnv (Class.cv f))).fv ∪ ((synCcnv (synCcnv (Class.cv f)))).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((synCcnv (Class.cv
        (nb068AlphaDummy000)))).fv ∪ ((synCcnv (synCcnv (Class.cv
        (nb068AlphaDummy000))))).fv) (by decide)) (freshVar_injective
        (((synCcnv (Class.cv f))).fv ∪ ((synCcnv (synCcnv (Class.cv f)))).fv) (by decide))
        (TAlphaVar.here _ _ _))))))))) (nb068SplitAlpha0148 x y f)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb068SplitAlpha0151 x y f))))))))
      (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.neg (nb068SplitAlpha0174 x y f))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb068AlphaDummy329) ≠ (nb068AlphaDummy486) from (by
                                        unfold nb068AlphaDummy486;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0512)
                                                1)))) (show (nb068AlphaDummy332 f) ≠
                                        (nb068AlphaDummy488 f) from (by
                                        unfold nb068AlphaDummy488;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0514 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy329) ≠ (nb068AlphaDummy485) from
                                        (by
                                          unfold nb068AlphaDummy485;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0512)
                                                  0)))) (show (nb068AlphaDummy332 f) ≠
        (nb068AlphaDummy487 f) from (by
                                          unfold nb068AlphaDummy487;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0514 f) 0))))
                                      (TAlphaVar.there (show (nb068AlphaDummy329) ≠
        (nb068AlphaDummy491) from (by
          unfold nb068AlphaDummy491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0516) 0)))) (show (nb068AlphaDummy332 f) ≠
        (nb068AlphaDummy492 f) from (by
          unfold nb068AlphaDummy492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0517 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy329) ≠ (nb068AlphaDummy489) from (by
          unfold nb068AlphaDummy489;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0513) 0)))) (show (nb068AlphaDummy332 f) ≠
        (nb068AlphaDummy490 f) from (by
          unfold nb068AlphaDummy490;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0515 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (nb068SplitAlpha0176 x y f)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb068AlphaDummy329) ≠ (nb068AlphaDummy486) from (by
                                        unfold nb068AlphaDummy486;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0512)
                                                1)))) (show (nb068AlphaDummy332 f) ≠
                                        (nb068AlphaDummy488 f) from (by
                                        unfold nb068AlphaDummy488;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0514 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy329) ≠ (nb068AlphaDummy485) from
                                        (by
                                          unfold nb068AlphaDummy485;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0512)
                                                  0)))) (show (nb068AlphaDummy332 f) ≠
        (nb068AlphaDummy487 f) from (by
                                          unfold nb068AlphaDummy487;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0514 f) 0))))
                                      (TAlphaVar.there (show (nb068AlphaDummy329) ≠
        (nb068AlphaDummy491) from (by
          unfold nb068AlphaDummy491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0516) 0)))) (show (nb068AlphaDummy332 f) ≠
        (nb068AlphaDummy492 f) from (by
          unfold nb068AlphaDummy492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0517 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy329) ≠ (nb068AlphaDummy489) from (by
          unfold nb068AlphaDummy489;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0513) 0)))) (show (nb068AlphaDummy332 f) ≠
        (nb068AlphaDummy490 f) from (by
          unfold nb068AlphaDummy490;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0515 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (nb068SplitAlpha0176 x y f)))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb068SplitAlpha0179 x y f))))))))
        (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.neg (nb068SplitAlpha0190 x y f))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0192`. -/
@[expose]
noncomputable def nb068SplitAlpha0192 (x : Var) (y : Var) (f : Var) (dv_f_x : f ≠ x)
    (dv_f_y : f ≠ y) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (synWf (Class.cv (nb068AlphaDummy000)) (Class.cv (nb068AlphaDummy001))
          (Class.cv (nb068AlphaDummy002)))
        (Wff.neg (synWfun (synCcnv (Class.cv (nb068AlphaDummy000))))))
      (Wff.imp (synWf (Class.cv f) (Class.cv x) (Class.cv y))
        (Wff.neg (synWfun (synCcnv (Class.cv f))))) :=
  (TAlphaWff.imp (TAlphaWff.conj (TAlphaWff.neg (nb068SplitAlpha0077 x y f dv_f_x dv_x_y))
      (TAlphaWff.classEq (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.neg (nb068SplitAlpha0083 x y f dv_f_y))))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb068AlphaDummy284), (nb068AlphaDummy286 f)),
                    ((nb068AlphaDummy283), (nb068AlphaDummy285 f)),
                    ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                    ((nb068AlphaDummy001), x),
                    ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                  (synCvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy284) ≠ (nb068AlphaDummy288) from (by
          unfold nb068AlphaDummy288;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0292) 1)))) (show (nb068AlphaDummy286 f) ≠
        (nb068AlphaDummy290 f) from (by
          unfold nb068AlphaDummy290;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0294 f) 1)))) (TAlphaVar.there (show
        (nb068AlphaDummy284) ≠ (nb068AlphaDummy287) from (by
          unfold nb068AlphaDummy287;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0292) 0)))) (show (nb068AlphaDummy286 f) ≠
        (nb068AlphaDummy289 f) from (by
          unfold nb068AlphaDummy289;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0294 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy284) ≠ (nb068AlphaDummy293) from (by
          unfold nb068AlphaDummy293;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0296) 0)))) (show (nb068AlphaDummy286 f) ≠
        (nb068AlphaDummy294 f) from (by
          unfold nb068AlphaDummy294;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0297 f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy284) ≠ (nb068AlphaDummy291)
        from (by
          unfold nb068AlphaDummy291;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0293)
                  0)))) (show (nb068AlphaDummy286 f) ≠ (nb068AlphaDummy292 f) from (by
          unfold nb068AlphaDummy292;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0295 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068SplitAlpha0085 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy284) ≠ (nb068AlphaDummy288) from (by
          unfold nb068AlphaDummy288;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0292) 1)))) (show (nb068AlphaDummy286 f) ≠
        (nb068AlphaDummy290 f) from (by
          unfold nb068AlphaDummy290;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0294 f) 1)))) (TAlphaVar.there (show
        (nb068AlphaDummy284) ≠ (nb068AlphaDummy287) from (by
          unfold nb068AlphaDummy287;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0292) 0)))) (show (nb068AlphaDummy286 f) ≠
        (nb068AlphaDummy289 f) from (by
          unfold nb068AlphaDummy289;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0294 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy284) ≠ (nb068AlphaDummy293) from (by
          unfold nb068AlphaDummy293;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0296) 0)))) (show (nb068AlphaDummy286 f) ≠
        (nb068AlphaDummy294 f) from (by
          unfold nb068AlphaDummy294;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0297 f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy284) ≠ (nb068AlphaDummy291)
        from (by
          unfold nb068AlphaDummy291;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0293)
                  0)))) (show (nb068AlphaDummy286 f) ≠ (nb068AlphaDummy292 f) from (by
          unfold nb068AlphaDummy292;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0295 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068SplitAlpha0085 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg
                            (TAlphaWff.neg (nb068SplitAlpha0088 x y f)))))))) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy284) from
                      (by
                        unfold nb068AlphaDummy284;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0334) 1))))
                    (show f ≠ (nb068AlphaDummy286 f) from (by
                        unfold nb068AlphaDummy286;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0335 f) 1)))) (TAlphaVar.there
                      (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy283) from (by
                          unfold nb068AlphaDummy283;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0334) 0))))
                      (show f ≠ (nb068AlphaDummy285 f) from (by
                          unfold nb068AlphaDummy285;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0335 f) 0))))
                      (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (nb068SplitAlpha0141 x y f))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (nb068SplitAlpha0141 x y f))))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
              (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
                        (show (nb068AlphaDummy328) ≠ (nb068AlphaDummy333) from (by
                            unfold nb068AlphaDummy333;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0342) 0))))) (Ne.symm
                        (show (nb068AlphaDummy331 f) ≠ (nb068AlphaDummy334 f) from (by
                            unfold nb068AlphaDummy334;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0343 f) 0)))))
                      (TAlphaVar.there (Ne.symm
                          (show (nb068AlphaDummy327) ≠ (nb068AlphaDummy333) from (by
                              unfold nb068AlphaDummy333;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0340) 0))))) (Ne.symm
                          (show (nb068AlphaDummy330 f) ≠ (nb068AlphaDummy334 f) from (by
                              unfold nb068AlphaDummy334;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0341 f) 0)))))
                        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb068AlphaDummy327) ≠ (nb068AlphaDummy336) from (by
          unfold nb068AlphaDummy336;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0344) 1)))) (show (nb068AlphaDummy330 f) ≠
        (nb068AlphaDummy338 f) from (by
          unfold nb068AlphaDummy338;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0346 f) 1)))) (TAlphaVar.there (show
        (nb068AlphaDummy327) ≠ (nb068AlphaDummy335) from (by
          unfold nb068AlphaDummy335;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0344) 0)))) (show (nb068AlphaDummy330 f) ≠
        (nb068AlphaDummy337 f) from (by
          unfold nb068AlphaDummy337;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0346 f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy327) ≠ (nb068AlphaDummy341)
        from (by
          unfold nb068AlphaDummy341;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0348)
                  0)))) (show (nb068AlphaDummy330 f) ≠ (nb068AlphaDummy342 f) from (by
          unfold nb068AlphaDummy342;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0349 f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy327) ≠ (nb068AlphaDummy339)
        from (by
          unfold nb068AlphaDummy339;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0345)
                  0)))) (show (nb068AlphaDummy330 f) ≠ (nb068AlphaDummy340 f) from (by
          unfold nb068AlphaDummy340;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0347 f)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (Class.cv
        (nb068AlphaDummy000)))).fv ∪ ((synCcnv (synCcnv (Class.cv
        (nb068AlphaDummy000))))).fv) (by decide)) (freshVar_injective
        (((synCcnv (Class.cv f))).fv ∪ ((synCcnv (synCcnv (Class.cv f)))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (nb068SplitAlpha0143 x y f))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb068AlphaDummy327) ≠ (nb068AlphaDummy336) from (by
          unfold nb068AlphaDummy336;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0344) 1)))) (show (nb068AlphaDummy330 f) ≠
        (nb068AlphaDummy338 f) from (by
          unfold nb068AlphaDummy338;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0346 f) 1)))) (TAlphaVar.there (show
        (nb068AlphaDummy327) ≠ (nb068AlphaDummy335) from (by
          unfold nb068AlphaDummy335;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0344) 0)))) (show (nb068AlphaDummy330 f) ≠
        (nb068AlphaDummy337 f) from (by
          unfold nb068AlphaDummy337;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0346 f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy327) ≠ (nb068AlphaDummy341)
        from (by
          unfold nb068AlphaDummy341;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0348)
                  0)))) (show (nb068AlphaDummy330 f) ≠ (nb068AlphaDummy342 f) from (by
          unfold nb068AlphaDummy342;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0349 f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy327) ≠ (nb068AlphaDummy339)
        from (by
          unfold nb068AlphaDummy339;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0345)
                  0)))) (show (nb068AlphaDummy330 f) ≠ (nb068AlphaDummy340 f) from (by
          unfold nb068AlphaDummy340;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0347 f)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (Class.cv
        (nb068AlphaDummy000)))).fv ∪ ((synCcnv (synCcnv (Class.cv
        (nb068AlphaDummy000))))).fv) (by decide)) (freshVar_injective
        (((synCcnv (Class.cv f))).fv ∪ ((synCcnv (synCcnv (Class.cv f)))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (nb068SplitAlpha0143 x y f)))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg
                              (TAlphaWff.neg (nb068SplitAlpha0146 x y f)))))))))
                (TAlphaWff.ex (TAlphaWff.neg (nb068SplitAlpha0191 x y f))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
