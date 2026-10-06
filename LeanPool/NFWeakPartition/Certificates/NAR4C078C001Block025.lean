/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block024

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part082`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0053`. -/
@[expose]
noncomputable def nb078SplitAlpha0053 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078AlphaDummy379), (nb078AlphaDummy380 g)),
        ((nb078AlphaDummy377), (nb078AlphaDummy378 g)),
        ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
        ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
        ((nb078AlphaDummy482), (nb078AlphaDummy484 g)),
        ((nb078AlphaDummy481), (nb078AlphaDummy483 g)),
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
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)), ((nb078AlphaDummy482),
        (nb078AlphaDummy484 g)), ((nb078AlphaDummy481), (nb078AlphaDummy483 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
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
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)), ((nb078AlphaDummy482),
        (nb078AlphaDummy484 g)), ((nb078AlphaDummy481), (nb078AlphaDummy483 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy381))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy383
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy399) from (by
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
                                    ((nb078AlphaDummy482), (nb078AlphaDummy484 g)),
                                    ((nb078AlphaDummy481), (nb078AlphaDummy483 g)),
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
                                    ((nb078AlphaDummy482), (nb078AlphaDummy484 g)),
                                    ((nb078AlphaDummy481), (nb078AlphaDummy483 g)),
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
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)), ((nb078AlphaDummy482),
        (nb078AlphaDummy484 g)), ((nb078AlphaDummy481), (nb078AlphaDummy483 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
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
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)), ((nb078AlphaDummy482),
        (nb078AlphaDummy484 g)), ((nb078AlphaDummy481), (nb078AlphaDummy483 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy381))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy383
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy399) from (by
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
                                      ((nb078AlphaDummy482), (nb078AlphaDummy484 g)),
                                      ((nb078AlphaDummy481), (nb078AlphaDummy483 g)),
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
                                      ((nb078AlphaDummy482), (nb078AlphaDummy484 g)),
                                      ((nb078AlphaDummy481), (nb078AlphaDummy483 g)),
                                      ((nb078AlphaDummy001), g),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part083`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0054`. -/
@[expose]
noncomputable def nb078SplitAlpha0054 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078AlphaDummy405), (nb078AlphaDummy406 g)),
        ((nb078AlphaDummy374), (nb078AlphaDummy376 g)),
        ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
        ((nb078AlphaDummy403), (nb078AlphaDummy404 g)),
        ((nb078AlphaDummy377), (nb078AlphaDummy378 g)),
        ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
        ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
        ((nb078AlphaDummy482), (nb078AlphaDummy484 g)),
        ((nb078AlphaDummy481), (nb078AlphaDummy483 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy405))
          (synCcompl (synCphi (Class.cv (nb078AlphaDummy374))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy405)) (synCcompl (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy406 g))
          (synCcompl (synCphi (Class.cv (nb078AlphaDummy376 g))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy406 g))
            (synCcompl (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
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
                            (TAlphaVar.there
                              (show (nb078AlphaDummy374) ≠ (nb078AlphaDummy407) from (by
                                  unfold nb078AlphaDummy407;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0410) 0))))
                              (show (nb078AlphaDummy376 g) ≠ (nb078AlphaDummy408 g) from
                                (by
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
                                          (mem_lt_freshVar (nb078_support_mem_0408) 0)))) (show
                                  (nb078AlphaDummy376 g) ≠ (nb078AlphaDummy406 g) from (by
                                    unfold nb078AlphaDummy406;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0409 g)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
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
        ((nb078AlphaDummy407), (nb078AlphaDummy408 g)), ((nb078AlphaDummy405),
        (nb078AlphaDummy406 g)), ((nb078AlphaDummy374), (nb078AlphaDummy376 g)),
        ((nb078AlphaDummy373), (nb078AlphaDummy375 g)), ((nb078AlphaDummy403),
        (nb078AlphaDummy404 g)), ((nb078AlphaDummy377), (nb078AlphaDummy378 g)),
        ((nb078AlphaDummy368), (nb078AlphaDummy370 g)), ((nb078AlphaDummy367),
        (nb078AlphaDummy369 g)), ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
        ((nb078AlphaDummy482), (nb078AlphaDummy484 g)), ((nb078AlphaDummy481),
        (nb078AlphaDummy483 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
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
        ((nb078AlphaDummy407), (nb078AlphaDummy408 g)), ((nb078AlphaDummy405),
        (nb078AlphaDummy406 g)), ((nb078AlphaDummy374), (nb078AlphaDummy376 g)),
        ((nb078AlphaDummy373), (nb078AlphaDummy375 g)), ((nb078AlphaDummy403),
        (nb078AlphaDummy404 g)), ((nb078AlphaDummy377), (nb078AlphaDummy378 g)),
        ((nb078AlphaDummy368), (nb078AlphaDummy370 g)), ((nb078AlphaDummy367),
        (nb078AlphaDummy369 g)), ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
        ((nb078AlphaDummy482), (nb078AlphaDummy484 g)), ((nb078AlphaDummy481),
        (nb078AlphaDummy483 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy381))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy383
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy399) from (by
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
                                    ((nb078AlphaDummy407), (nb078AlphaDummy408 g)),
                                    ((nb078AlphaDummy405), (nb078AlphaDummy406 g)),
                                    ((nb078AlphaDummy374), (nb078AlphaDummy376 g)),
                                    ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
                                    ((nb078AlphaDummy403), (nb078AlphaDummy404 g)),
                                    ((nb078AlphaDummy377), (nb078AlphaDummy378 g)),
                                    ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
                                    ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
                                    ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
                                    ((nb078AlphaDummy482), (nb078AlphaDummy484 g)),
                                    ((nb078AlphaDummy481), (nb078AlphaDummy483 g)),
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
                                    ((nb078AlphaDummy407), (nb078AlphaDummy408 g)),
                                    ((nb078AlphaDummy405), (nb078AlphaDummy406 g)),
                                    ((nb078AlphaDummy374), (nb078AlphaDummy376 g)),
                                    ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
                                    ((nb078AlphaDummy403), (nb078AlphaDummy404 g)),
                                    ((nb078AlphaDummy377), (nb078AlphaDummy378 g)),
                                    ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
                                    ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
                                    ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
                                    ((nb078AlphaDummy482), (nb078AlphaDummy484 g)),
                                    ((nb078AlphaDummy481), (nb078AlphaDummy483 g)),
                                    ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
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
                            (TAlphaVar.there
                              (show (nb078AlphaDummy374) ≠ (nb078AlphaDummy407) from (by
                                  unfold nb078AlphaDummy407;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0410) 0))))
                              (show (nb078AlphaDummy376 g) ≠ (nb078AlphaDummy408 g) from
                                (by
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
                                          (mem_lt_freshVar (nb078_support_mem_0408) 0)))) (show
                                  (nb078AlphaDummy376 g) ≠ (nb078AlphaDummy406 g) from (by
                                    unfold nb078AlphaDummy406;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0409 g)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
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
        ((nb078AlphaDummy407), (nb078AlphaDummy408 g)), ((nb078AlphaDummy405),
        (nb078AlphaDummy406 g)), ((nb078AlphaDummy374), (nb078AlphaDummy376 g)),
        ((nb078AlphaDummy373), (nb078AlphaDummy375 g)), ((nb078AlphaDummy403),
        (nb078AlphaDummy404 g)), ((nb078AlphaDummy377), (nb078AlphaDummy378 g)),
        ((nb078AlphaDummy368), (nb078AlphaDummy370 g)), ((nb078AlphaDummy367),
        (nb078AlphaDummy369 g)), ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
        ((nb078AlphaDummy482), (nb078AlphaDummy484 g)), ((nb078AlphaDummy481),
        (nb078AlphaDummy483 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
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
        ((nb078AlphaDummy407), (nb078AlphaDummy408 g)), ((nb078AlphaDummy405),
        (nb078AlphaDummy406 g)), ((nb078AlphaDummy374), (nb078AlphaDummy376 g)),
        ((nb078AlphaDummy373), (nb078AlphaDummy375 g)), ((nb078AlphaDummy403),
        (nb078AlphaDummy404 g)), ((nb078AlphaDummy377), (nb078AlphaDummy378 g)),
        ((nb078AlphaDummy368), (nb078AlphaDummy370 g)), ((nb078AlphaDummy367),
        (nb078AlphaDummy369 g)), ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
        ((nb078AlphaDummy482), (nb078AlphaDummy484 g)), ((nb078AlphaDummy481),
        (nb078AlphaDummy483 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy381))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy383
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy399) from (by
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
                                    ((nb078AlphaDummy407), (nb078AlphaDummy408 g)),
                                    ((nb078AlphaDummy405), (nb078AlphaDummy406 g)),
                                    ((nb078AlphaDummy374), (nb078AlphaDummy376 g)),
                                    ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
                                    ((nb078AlphaDummy403), (nb078AlphaDummy404 g)),
                                    ((nb078AlphaDummy377), (nb078AlphaDummy378 g)),
                                    ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
                                    ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
                                    ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
                                    ((nb078AlphaDummy482), (nb078AlphaDummy484 g)),
                                    ((nb078AlphaDummy481), (nb078AlphaDummy483 g)),
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
                                    ((nb078AlphaDummy407), (nb078AlphaDummy408 g)),
                                    ((nb078AlphaDummy405), (nb078AlphaDummy406 g)),
                                    ((nb078AlphaDummy374), (nb078AlphaDummy376 g)),
                                    ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
                                    ((nb078AlphaDummy403), (nb078AlphaDummy404 g)),
                                    ((nb078AlphaDummy377), (nb078AlphaDummy378 g)),
                                    ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
                                    ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
                                    ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
                                    ((nb078AlphaDummy482), (nb078AlphaDummy484 g)),
                                    ((nb078AlphaDummy481), (nb078AlphaDummy483 g)),
                                    ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.reflOfClosed [((nb078AlphaDummy405), (nb078AlphaDummy406 g)),
            ((nb078AlphaDummy374), (nb078AlphaDummy376 g)),
            ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
            ((nb078AlphaDummy403), (nb078AlphaDummy404 g)),
            ((nb078AlphaDummy377), (nb078AlphaDummy378 g)),
            ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
            ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
            ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
            ((nb078AlphaDummy482), (nb078AlphaDummy484 g)),
            ((nb078AlphaDummy481), (nb078AlphaDummy483 g)),
            ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
            ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part084`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0055`. -/
@[expose]
noncomputable def nb078SplitAlpha0055 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078AlphaDummy415), (nb078AlphaDummy416 g)),
        ((nb078AlphaDummy413), (nb078AlphaDummy414 g)),
        ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
        ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
        ((nb078AlphaDummy482), (nb078AlphaDummy484 g)),
        ((nb078AlphaDummy481), (nb078AlphaDummy483 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy415))
          (Class.cab (nb078AlphaDummy409)
            (synWrex (nb078AlphaDummy410) (Class.cv (nb078AlphaDummy368))
              (Wff.classEq (Class.cv (nb078AlphaDummy409))
                (synCphi (Class.cv (nb078AlphaDummy410))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy415)) (Class.cab (nb078AlphaDummy409)
              (synWrex (nb078AlphaDummy410) (Class.cv (nb078AlphaDummy368))
                (Wff.classEq (Class.cv (nb078AlphaDummy409))
                  (synCphi (Class.cv (nb078AlphaDummy410)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy416 g))
          (Class.cab (nb078AlphaDummy411 g)
            (synWrex (nb078AlphaDummy412 g) (Class.cv (nb078AlphaDummy370 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy411 g))
                (synCphi (Class.cv (nb078AlphaDummy412 g))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy416 g))
            (Class.cab (nb078AlphaDummy411 g)
              (synWrex (nb078AlphaDummy412 g) (Class.cv (nb078AlphaDummy370 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy411 g))
                  (synCphi (Class.cv (nb078AlphaDummy412 g))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy368) ≠ (nb078AlphaDummy410) from
                    (by
                      unfold nb078AlphaDummy410;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0412) 1))))
                  (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy412 g) from (by
                      unfold nb078AlphaDummy412;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0414 g) 1))))
                  (TAlphaVar.there (show (nb078AlphaDummy368) ≠ (nb078AlphaDummy409) from
                      (by
                        unfold nb078AlphaDummy409;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0412) 0))))
                    (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy411 g) from (by
                        unfold nb078AlphaDummy411;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0414 g) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy368) ≠ (nb078AlphaDummy415) from (by
                          unfold nb078AlphaDummy415;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0416) 0))))
                      (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy416 g) from (by
                          unfold nb078AlphaDummy416;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0417 g) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy368) ≠ (nb078AlphaDummy413) from (by
                            unfold nb078AlphaDummy413;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0413) 0))))
                        (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy414 g) from (by
                            unfold nb078AlphaDummy414;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0415 g) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy368))).fv ∪
                      ((Class.cv (nb078AlphaDummy367))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078AlphaDummy370 g))).fv ∪
                      ((Class.cv (nb078AlphaDummy369 g))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy410) ≠ (nb078AlphaDummy417) from (by
                              unfold nb078AlphaDummy417;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0418) 0))))
                          (show (nb078AlphaDummy412 g) ≠ (nb078AlphaDummy419 g) from (by
                              unfold nb078AlphaDummy419;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0419 g) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy410) ≠ (nb078AlphaDummy418) from (by
                                unfold nb078AlphaDummy418;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0418) 1))))
                            (show (nb078AlphaDummy412 g) ≠ (nb078AlphaDummy420 g) from (by
                                unfold nb078AlphaDummy420;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0419 g) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy410))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy412 g))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy417) ≠ (nb078AlphaDummy424) from (by
          unfold nb078AlphaDummy424;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0422) 1)))) (show (nb078AlphaDummy419 g) ≠
        (nb078AlphaDummy427 g) from (by
          unfold nb078AlphaDummy427;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0423 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy417) ≠ (nb078AlphaDummy423) from (by
          unfold nb078AlphaDummy423;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0422) 0)))) (show (nb078AlphaDummy419 g) ≠
        (nb078AlphaDummy426 g) from (by
          unfold nb078AlphaDummy426;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0423 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy417) ≠ (nb078AlphaDummy421) from (by
          unfold nb078AlphaDummy421;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0420) 0)))) (show (nb078AlphaDummy419 g) ≠
        (nb078AlphaDummy422 g) from (by
          unfold nb078AlphaDummy422;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0421 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy425), (nb078AlphaDummy428 g)), ((nb078AlphaDummy424),
        (nb078AlphaDummy427 g)), ((nb078AlphaDummy423), (nb078AlphaDummy426 g)),
        ((nb078AlphaDummy421), (nb078AlphaDummy422 g)), ((nb078AlphaDummy417),
        (nb078AlphaDummy419 g)), ((nb078AlphaDummy418), (nb078AlphaDummy420 g)),
        ((nb078AlphaDummy410), (nb078AlphaDummy412 g)), ((nb078AlphaDummy409),
        (nb078AlphaDummy411 g)), ((nb078AlphaDummy415), (nb078AlphaDummy416 g)),
        ((nb078AlphaDummy413), (nb078AlphaDummy414 g)), ((nb078AlphaDummy368),
        (nb078AlphaDummy370 g)), ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)), ((nb078AlphaDummy482),
        (nb078AlphaDummy484 g)), ((nb078AlphaDummy481), (nb078AlphaDummy483 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy424) ≠ (nb078AlphaDummy431) from (by
          unfold
            nb078AlphaDummy431;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0426)
                  0)))) (show (nb078AlphaDummy427 g) ≠ (nb078AlphaDummy432 g) from (by
          unfold
            nb078AlphaDummy432;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0427
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy424) ≠ (nb078AlphaDummy429)
        from (by
          unfold
            nb078AlphaDummy429;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0424)
                  0)))) (show (nb078AlphaDummy427 g) ≠ (nb078AlphaDummy430 g) from (by
          unfold
            nb078AlphaDummy430;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0425
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy417))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy419 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy425) ≠ (nb078AlphaDummy431)
        from (by
          unfold
            nb078AlphaDummy431;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0430)
                  0)))) (show (nb078AlphaDummy428 g) ≠ (nb078AlphaDummy432 g) from (by
          unfold
            nb078AlphaDummy432;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0431
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy425) ≠ (nb078AlphaDummy429)
        from (by
          unfold
            nb078AlphaDummy429;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0428)
                  0)))) (show (nb078AlphaDummy428 g) ≠ (nb078AlphaDummy430 g) from (by
          unfold
            nb078AlphaDummy430;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0429
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy424) ≠ (nb078AlphaDummy431) from (by
          unfold
            nb078AlphaDummy431;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0426)
                  0)))) (show (nb078AlphaDummy427 g) ≠ (nb078AlphaDummy432 g) from (by
          unfold
            nb078AlphaDummy432;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0427
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy424) ≠ (nb078AlphaDummy429)
        from (by
          unfold
            nb078AlphaDummy429;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0424)
                  0)))) (show (nb078AlphaDummy427 g) ≠ (nb078AlphaDummy430 g) from (by
          unfold
            nb078AlphaDummy430;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0425
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy417))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy419 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy425) ≠ (nb078AlphaDummy431)
        from (by
          unfold
            nb078AlphaDummy431;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0430)
                  0)))) (show (nb078AlphaDummy428 g) ≠ (nb078AlphaDummy432 g) from (by
          unfold
            nb078AlphaDummy432;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0431
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy425) ≠ (nb078AlphaDummy429)
        from (by
          unfold
            nb078AlphaDummy429;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0428)
                  0)))) (show (nb078AlphaDummy428 g) ≠ (nb078AlphaDummy430 g) from (by
          unfold
            nb078AlphaDummy430;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0429
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy425), (nb078AlphaDummy428 g)), ((nb078AlphaDummy424),
        (nb078AlphaDummy427 g)), ((nb078AlphaDummy423), (nb078AlphaDummy426 g)),
        ((nb078AlphaDummy421), (nb078AlphaDummy422 g)), ((nb078AlphaDummy417),
        (nb078AlphaDummy419 g)), ((nb078AlphaDummy418), (nb078AlphaDummy420 g)),
        ((nb078AlphaDummy410), (nb078AlphaDummy412 g)), ((nb078AlphaDummy409),
        (nb078AlphaDummy411 g)), ((nb078AlphaDummy415), (nb078AlphaDummy416 g)),
        ((nb078AlphaDummy413), (nb078AlphaDummy414 g)), ((nb078AlphaDummy368),
        (nb078AlphaDummy370 g)), ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)), ((nb078AlphaDummy482),
        (nb078AlphaDummy484 g)), ((nb078AlphaDummy481), (nb078AlphaDummy483 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy417))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy419 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy417))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy419
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy424) ≠ (nb078AlphaDummy435) from (by
          unfold
            nb078AlphaDummy435;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0434)
                  0)))) (show (nb078AlphaDummy427 g) ≠ (nb078AlphaDummy436 g) from (by
          unfold
            nb078AlphaDummy436;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0435
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy424) ≠ (nb078AlphaDummy433)
        from (by
          unfold
            nb078AlphaDummy433;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0432)
                  0)))) (show (nb078AlphaDummy427 g) ≠ (nb078AlphaDummy434 g) from (by
          unfold
            nb078AlphaDummy434;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0433
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy417))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy419 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy424) ≠ (nb078AlphaDummy435)
        from (by
          unfold
            nb078AlphaDummy435;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0434)
                  0)))) (show (nb078AlphaDummy427 g) ≠ (nb078AlphaDummy436 g) from (by
          unfold
            nb078AlphaDummy436;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0435
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy424) ≠ (nb078AlphaDummy433)
        from (by
          unfold
            nb078AlphaDummy433;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0432)
                  0)))) (show (nb078AlphaDummy427 g) ≠ (nb078AlphaDummy434 g) from (by
          unfold
            nb078AlphaDummy434;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0433
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy417))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy419 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy425) ≠ (nb078AlphaDummy437) from (by
          unfold
            nb078AlphaDummy437;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0438)
                  0)))) (show (nb078AlphaDummy428 g) ≠ (nb078AlphaDummy438 g) from (by
          unfold
            nb078AlphaDummy438;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0439
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy425) ≠ (nb078AlphaDummy433)
        from (by
          unfold
            nb078AlphaDummy433;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0436)
                  0)))) (show (nb078AlphaDummy428 g) ≠ (nb078AlphaDummy434 g) from (by
          unfold
            nb078AlphaDummy434;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0437
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy425) ≠
        (nb078AlphaDummy437) from (by
          unfold
            nb078AlphaDummy437;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0438)
                  0)))) (show (nb078AlphaDummy428 g) ≠ (nb078AlphaDummy438 g) from (by
          unfold
            nb078AlphaDummy438;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0439
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy425) ≠ (nb078AlphaDummy433)
        from (by
          unfold
            nb078AlphaDummy433;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0436)
                  0)))) (show (nb078AlphaDummy428 g) ≠ (nb078AlphaDummy434 g) from (by
          unfold
            nb078AlphaDummy434;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0437
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy417) ≠ (nb078AlphaDummy421) from (by
                                        unfold nb078AlphaDummy421;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0420)
                                                0)))) (show (nb078AlphaDummy419 g) ≠
                                        (nb078AlphaDummy422 g) from (by
                                        unfold nb078AlphaDummy422;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0421 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy421), (nb078AlphaDummy422 g)),
                                    ((nb078AlphaDummy417), (nb078AlphaDummy419 g)),
                                    ((nb078AlphaDummy418), (nb078AlphaDummy420 g)),
                                    ((nb078AlphaDummy410), (nb078AlphaDummy412 g)),
                                    ((nb078AlphaDummy409), (nb078AlphaDummy411 g)),
                                    ((nb078AlphaDummy415), (nb078AlphaDummy416 g)),
                                    ((nb078AlphaDummy413), (nb078AlphaDummy414 g)),
                                    ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
                                    ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
                                    ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
                                    ((nb078AlphaDummy482), (nb078AlphaDummy484 g)),
                                    ((nb078AlphaDummy481), (nb078AlphaDummy483 g)),
                                    ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy417) ≠ (nb078AlphaDummy421) from
                                    (by
                                      unfold nb078AlphaDummy421;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0420)
                                              0)))) (show
                                    (nb078AlphaDummy419 g) ≠ (nb078AlphaDummy422 g) from
                                    (by
                                      unfold nb078AlphaDummy422;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0421 g)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy417) ≠ (nb078AlphaDummy421) from (by
                                        unfold nb078AlphaDummy421;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0420)
                                                0)))) (show (nb078AlphaDummy419 g) ≠
                                        (nb078AlphaDummy422 g) from (by
                                        unfold nb078AlphaDummy422;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0421 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy421), (nb078AlphaDummy422 g)),
                                    ((nb078AlphaDummy417), (nb078AlphaDummy419 g)),
                                    ((nb078AlphaDummy418), (nb078AlphaDummy420 g)),
                                    ((nb078AlphaDummy410), (nb078AlphaDummy412 g)),
                                    ((nb078AlphaDummy409), (nb078AlphaDummy411 g)),
                                    ((nb078AlphaDummy415), (nb078AlphaDummy416 g)),
                                    ((nb078AlphaDummy413), (nb078AlphaDummy414 g)),
                                    ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
                                    ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
                                    ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
                                    ((nb078AlphaDummy482), (nb078AlphaDummy484 g)),
                                    ((nb078AlphaDummy481), (nb078AlphaDummy483 g)),
                                    ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078AlphaDummy368) ≠ (nb078AlphaDummy410) from
                      (by
                        unfold nb078AlphaDummy410;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0412) 1))))
                    (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy412 g) from (by
                        unfold nb078AlphaDummy412;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0414 g) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy368) ≠ (nb078AlphaDummy409) from (by
                          unfold nb078AlphaDummy409;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0412) 0))))
                      (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy411 g) from (by
                          unfold nb078AlphaDummy411;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0414 g) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy368) ≠ (nb078AlphaDummy415) from (by
                            unfold nb078AlphaDummy415;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0416) 0))))
                        (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy416 g) from (by
                            unfold nb078AlphaDummy416;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0417 g) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy368) ≠ (nb078AlphaDummy413) from (by
                              unfold nb078AlphaDummy413;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0413) 0))))
                          (show (nb078AlphaDummy370 g) ≠ (nb078AlphaDummy414 g) from (by
                              unfold nb078AlphaDummy414;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0415 g) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078AlphaDummy368))).fv ∪
                        ((Class.cv (nb078AlphaDummy367))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy370 g))).fv ∪
                        ((Class.cv (nb078AlphaDummy369 g))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy410) ≠ (nb078AlphaDummy417) from (by
                                unfold nb078AlphaDummy417;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0418) 0))))
                            (show (nb078AlphaDummy412 g) ≠ (nb078AlphaDummy419 g) from (by
                                unfold nb078AlphaDummy419;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0419 g) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy410) ≠ (nb078AlphaDummy418) from (by
                                  unfold nb078AlphaDummy418;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0418) 1))))
                              (show (nb078AlphaDummy412 g) ≠ (nb078AlphaDummy420 g) from
                                (by
                                  unfold nb078AlphaDummy420;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0419 g) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy410))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy412 g))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy417) ≠ (nb078AlphaDummy424) from (by
          unfold nb078AlphaDummy424;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0422) 1)))) (show (nb078AlphaDummy419 g) ≠
        (nb078AlphaDummy427 g) from (by
          unfold nb078AlphaDummy427;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0423 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy417) ≠ (nb078AlphaDummy423) from (by
          unfold nb078AlphaDummy423;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0422) 0)))) (show (nb078AlphaDummy419 g) ≠
        (nb078AlphaDummy426 g) from (by
          unfold nb078AlphaDummy426;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0423 g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy417) ≠ (nb078AlphaDummy421)
        from (by
          unfold nb078AlphaDummy421;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0420)
                  0)))) (show (nb078AlphaDummy419 g) ≠ (nb078AlphaDummy422 g) from (by
          unfold nb078AlphaDummy422;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0421 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy425), (nb078AlphaDummy428 g)), ((nb078AlphaDummy424),
        (nb078AlphaDummy427 g)), ((nb078AlphaDummy423), (nb078AlphaDummy426 g)),
        ((nb078AlphaDummy421), (nb078AlphaDummy422 g)), ((nb078AlphaDummy417),
        (nb078AlphaDummy419 g)), ((nb078AlphaDummy418), (nb078AlphaDummy420 g)),
        ((nb078AlphaDummy410), (nb078AlphaDummy412 g)), ((nb078AlphaDummy409),
        (nb078AlphaDummy411 g)), ((nb078AlphaDummy415), (nb078AlphaDummy416 g)),
        ((nb078AlphaDummy413), (nb078AlphaDummy414 g)), ((nb078AlphaDummy368),
        (nb078AlphaDummy370 g)), ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)), ((nb078AlphaDummy482),
        (nb078AlphaDummy484 g)), ((nb078AlphaDummy481), (nb078AlphaDummy483 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy424) ≠ (nb078AlphaDummy431) from (by
          unfold
            nb078AlphaDummy431;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0426)
                  0)))) (show (nb078AlphaDummy427 g) ≠ (nb078AlphaDummy432 g) from (by
          unfold
            nb078AlphaDummy432;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0427
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy424) ≠ (nb078AlphaDummy429)
        from (by
          unfold
            nb078AlphaDummy429;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0424)
                  0)))) (show (nb078AlphaDummy427 g) ≠ (nb078AlphaDummy430 g) from (by
          unfold
            nb078AlphaDummy430;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0425
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy417))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy419 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy425) ≠ (nb078AlphaDummy431)
        from (by
          unfold
            nb078AlphaDummy431;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0430)
                  0)))) (show (nb078AlphaDummy428 g) ≠ (nb078AlphaDummy432 g) from (by
          unfold
            nb078AlphaDummy432;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0431
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy425) ≠ (nb078AlphaDummy429)
        from (by
          unfold
            nb078AlphaDummy429;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0428)
                  0)))) (show (nb078AlphaDummy428 g) ≠ (nb078AlphaDummy430 g) from (by
          unfold
            nb078AlphaDummy430;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0429
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy424) ≠ (nb078AlphaDummy431) from (by
          unfold
            nb078AlphaDummy431;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0426)
                  0)))) (show (nb078AlphaDummy427 g) ≠ (nb078AlphaDummy432 g) from (by
          unfold
            nb078AlphaDummy432;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0427
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy424) ≠ (nb078AlphaDummy429)
        from (by
          unfold
            nb078AlphaDummy429;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0424)
                  0)))) (show (nb078AlphaDummy427 g) ≠ (nb078AlphaDummy430 g) from (by
          unfold
            nb078AlphaDummy430;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0425
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy417))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy419 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy425) ≠ (nb078AlphaDummy431)
        from (by
          unfold
            nb078AlphaDummy431;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0430)
                  0)))) (show (nb078AlphaDummy428 g) ≠ (nb078AlphaDummy432 g) from (by
          unfold
            nb078AlphaDummy432;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0431
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy425) ≠ (nb078AlphaDummy429)
        from (by
          unfold
            nb078AlphaDummy429;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0428)
                  0)))) (show (nb078AlphaDummy428 g) ≠ (nb078AlphaDummy430 g) from (by
          unfold
            nb078AlphaDummy430;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0429
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy425), (nb078AlphaDummy428 g)), ((nb078AlphaDummy424),
        (nb078AlphaDummy427 g)), ((nb078AlphaDummy423), (nb078AlphaDummy426 g)),
        ((nb078AlphaDummy421), (nb078AlphaDummy422 g)), ((nb078AlphaDummy417),
        (nb078AlphaDummy419 g)), ((nb078AlphaDummy418), (nb078AlphaDummy420 g)),
        ((nb078AlphaDummy410), (nb078AlphaDummy412 g)), ((nb078AlphaDummy409),
        (nb078AlphaDummy411 g)), ((nb078AlphaDummy415), (nb078AlphaDummy416 g)),
        ((nb078AlphaDummy413), (nb078AlphaDummy414 g)), ((nb078AlphaDummy368),
        (nb078AlphaDummy370 g)), ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)), ((nb078AlphaDummy482),
        (nb078AlphaDummy484 g)), ((nb078AlphaDummy481), (nb078AlphaDummy483 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy417))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy419 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy417))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy419
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy424) ≠ (nb078AlphaDummy435) from (by
          unfold
            nb078AlphaDummy435;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0434)
                  0)))) (show (nb078AlphaDummy427 g) ≠ (nb078AlphaDummy436 g) from (by
          unfold
            nb078AlphaDummy436;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0435
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy424) ≠ (nb078AlphaDummy433)
        from (by
          unfold
            nb078AlphaDummy433;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0432)
                  0)))) (show (nb078AlphaDummy427 g) ≠ (nb078AlphaDummy434 g) from (by
          unfold
            nb078AlphaDummy434;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0433
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy417))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy419 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy424) ≠ (nb078AlphaDummy435)
        from (by
          unfold
            nb078AlphaDummy435;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0434)
                  0)))) (show (nb078AlphaDummy427 g) ≠ (nb078AlphaDummy436 g) from (by
          unfold
            nb078AlphaDummy436;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0435
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy424) ≠ (nb078AlphaDummy433)
        from (by
          unfold
            nb078AlphaDummy433;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0432)
                  0)))) (show (nb078AlphaDummy427 g) ≠ (nb078AlphaDummy434 g) from (by
          unfold
            nb078AlphaDummy434;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0433
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy417))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy419 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy425) ≠ (nb078AlphaDummy437) from (by
          unfold
            nb078AlphaDummy437;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0438)
                  0)))) (show (nb078AlphaDummy428 g) ≠ (nb078AlphaDummy438 g) from (by
          unfold
            nb078AlphaDummy438;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0439
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy425) ≠ (nb078AlphaDummy433)
        from (by
          unfold
            nb078AlphaDummy433;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0436)
                  0)))) (show (nb078AlphaDummy428 g) ≠ (nb078AlphaDummy434 g) from (by
          unfold
            nb078AlphaDummy434;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0437
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy425) ≠
        (nb078AlphaDummy437) from (by
          unfold
            nb078AlphaDummy437;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0438)
                  0)))) (show (nb078AlphaDummy428 g) ≠ (nb078AlphaDummy438 g) from (by
          unfold
            nb078AlphaDummy438;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0439
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy425) ≠ (nb078AlphaDummy433)
        from (by
          unfold
            nb078AlphaDummy433;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0436)
                  0)))) (show (nb078AlphaDummy428 g) ≠ (nb078AlphaDummy434 g) from (by
          unfold
            nb078AlphaDummy434;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0437
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy417) ≠ (nb078AlphaDummy421) from
                                        (by
                                          unfold nb078AlphaDummy421;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0420)
                                                  0)))) (show (nb078AlphaDummy419 g) ≠
        (nb078AlphaDummy422 g) from (by
                                          unfold nb078AlphaDummy422;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0421 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy421), (nb078AlphaDummy422 g)),
                                      ((nb078AlphaDummy417), (nb078AlphaDummy419 g)),
                                      ((nb078AlphaDummy418), (nb078AlphaDummy420 g)),
                                      ((nb078AlphaDummy410), (nb078AlphaDummy412 g)),
                                      ((nb078AlphaDummy409), (nb078AlphaDummy411 g)),
                                      ((nb078AlphaDummy415), (nb078AlphaDummy416 g)),
                                      ((nb078AlphaDummy413), (nb078AlphaDummy414 g)),
                                      ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
                                      ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
                                      ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
                                      ((nb078AlphaDummy482), (nb078AlphaDummy484 g)),
                                      ((nb078AlphaDummy481), (nb078AlphaDummy483 g)),
                                      ((nb078AlphaDummy001), g),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy417) ≠ (nb078AlphaDummy421) from (by
                                        unfold nb078AlphaDummy421;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0420)
                                                0)))) (show (nb078AlphaDummy419 g) ≠
                                        (nb078AlphaDummy422 g) from (by
                                        unfold nb078AlphaDummy422;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0421 g)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy417) ≠ (nb078AlphaDummy421) from
                                        (by
                                          unfold nb078AlphaDummy421;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0420)
                                                  0)))) (show (nb078AlphaDummy419 g) ≠
        (nb078AlphaDummy422 g) from (by
                                          unfold nb078AlphaDummy422;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0421 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy421), (nb078AlphaDummy422 g)),
                                      ((nb078AlphaDummy417), (nb078AlphaDummy419 g)),
                                      ((nb078AlphaDummy418), (nb078AlphaDummy420 g)),
                                      ((nb078AlphaDummy410), (nb078AlphaDummy412 g)),
                                      ((nb078AlphaDummy409), (nb078AlphaDummy411 g)),
                                      ((nb078AlphaDummy415), (nb078AlphaDummy416 g)),
                                      ((nb078AlphaDummy413), (nb078AlphaDummy414 g)),
                                      ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
                                      ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
                                      ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
                                      ((nb078AlphaDummy482), (nb078AlphaDummy484 g)),
                                      ((nb078AlphaDummy481), (nb078AlphaDummy483 g)),
                                      ((nb078AlphaDummy001), g),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
