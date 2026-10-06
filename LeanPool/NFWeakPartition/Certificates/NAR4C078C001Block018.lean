/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4C078C001Part060Stage1

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part060`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0030`. -/
@[expose]
noncomputable def nb078SplitAlpha0030 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078AlphaDummy301), (nb078AlphaDummy302 g)),
        ((nb078AlphaDummy299), (nb078AlphaDummy300 g)),
        ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
        ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
        ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
        ((nb078AlphaDummy285), (nb078AlphaDummy286 g)),
        ((nb078AlphaDummy283), (nb078AlphaDummy284 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy301))
          (Class.cab (nb078AlphaDummy295)
            (synWrex (nb078AlphaDummy296) (Class.cv (nb078AlphaDummy287))
              (Wff.classEq (Class.cv (nb078AlphaDummy295))
                (synCphi (Class.cv (nb078AlphaDummy296))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy301)) (Class.cab (nb078AlphaDummy295)
              (synWrex (nb078AlphaDummy296) (Class.cv (nb078AlphaDummy287))
                (Wff.classEq (Class.cv (nb078AlphaDummy295))
                  (synCphi (Class.cv (nb078AlphaDummy296)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy302 g))
          (Class.cab (nb078AlphaDummy297 g)
            (synWrex (nb078AlphaDummy298 g) (Class.cv (nb078AlphaDummy290 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy297 g))
                (synCphi (Class.cv (nb078AlphaDummy298 g))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy302 g))
            (Class.cab (nb078AlphaDummy297 g)
              (synWrex (nb078AlphaDummy298 g) (Class.cv (nb078AlphaDummy290 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy297 g))
                  (synCphi (Class.cv (nb078AlphaDummy298 g))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy287) ≠ (nb078AlphaDummy296) from
                    (by
                      unfold nb078AlphaDummy296;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0294) 1))))
                  (show (nb078AlphaDummy290 g) ≠ (nb078AlphaDummy298 g) from (by
                      unfold nb078AlphaDummy298;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0296 g) 1))))
                  (TAlphaVar.there (show (nb078AlphaDummy287) ≠ (nb078AlphaDummy295) from
                      (by
                        unfold nb078AlphaDummy295;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0294) 0))))
                    (show (nb078AlphaDummy290 g) ≠ (nb078AlphaDummy297 g) from (by
                        unfold nb078AlphaDummy297;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0296 g) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy287) ≠ (nb078AlphaDummy301) from (by
                          unfold nb078AlphaDummy301;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0298) 0))))
                      (show (nb078AlphaDummy290 g) ≠ (nb078AlphaDummy302 g) from (by
                          unfold nb078AlphaDummy302;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0299 g) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy287) ≠ (nb078AlphaDummy299) from (by
                            unfold nb078AlphaDummy299;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0295) 0))))
                        (show (nb078AlphaDummy290 g) ≠ (nb078AlphaDummy300 g) from (by
                            unfold nb078AlphaDummy300;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0297 g) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb078AlphaDummy001))).fv ∪
                              ((synCcnv (Class.cv (nb078AlphaDummy001)))).fv) (by decide))
                          (freshVar_injective (((Class.cv g)).fv ∪ ((synCcnv (Class.cv g))).fv)
                            (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb078AlphaDummy287))).fv ∪
                      ((Class.cv (nb078AlphaDummy288))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078AlphaDummy290 g))).fv ∪
                      ((Class.cv (nb078AlphaDummy291 g))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy296) ≠ (nb078AlphaDummy303) from (by
                              unfold nb078AlphaDummy303;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0300) 0))))
                          (show (nb078AlphaDummy298 g) ≠ (nb078AlphaDummy305 g) from (by
                              unfold nb078AlphaDummy305;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0301 g) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy296) ≠ (nb078AlphaDummy304) from (by
                                unfold nb078AlphaDummy304;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0300) 1))))
                            (show (nb078AlphaDummy298 g) ≠ (nb078AlphaDummy306 g) from (by
                                unfold nb078AlphaDummy306;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0301 g) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy296))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy298 g))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy303) ≠ (nb078AlphaDummy310) from (by
          unfold nb078AlphaDummy310;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0304) 1)))) (show (nb078AlphaDummy305 g) ≠
        (nb078AlphaDummy313 g) from (by
          unfold nb078AlphaDummy313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0305 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy303) ≠ (nb078AlphaDummy309) from (by
          unfold nb078AlphaDummy309;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0304) 0)))) (show (nb078AlphaDummy305 g) ≠
        (nb078AlphaDummy312 g) from (by
          unfold nb078AlphaDummy312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0305 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy303) ≠ (nb078AlphaDummy307) from (by
          unfold nb078AlphaDummy307;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0302) 0)))) (show (nb078AlphaDummy305 g) ≠
        (nb078AlphaDummy308 g) from (by
          unfold nb078AlphaDummy308;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0303 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy311), (nb078AlphaDummy314 g)), ((nb078AlphaDummy310),
        (nb078AlphaDummy313 g)), ((nb078AlphaDummy309), (nb078AlphaDummy312 g)),
        ((nb078AlphaDummy307), (nb078AlphaDummy308 g)), ((nb078AlphaDummy303),
        (nb078AlphaDummy305 g)), ((nb078AlphaDummy304), (nb078AlphaDummy306 g)),
        ((nb078AlphaDummy296), (nb078AlphaDummy298 g)), ((nb078AlphaDummy295),
        (nb078AlphaDummy297 g)), ((nb078AlphaDummy301), (nb078AlphaDummy302 g)),
        ((nb078AlphaDummy299), (nb078AlphaDummy300 g)), ((nb078AlphaDummy288),
        (nb078AlphaDummy291 g)), ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
        ((nb078AlphaDummy293), (nb078AlphaDummy294 g)), ((nb078AlphaDummy285),
        (nb078AlphaDummy286 g)), ((nb078AlphaDummy283), (nb078AlphaDummy284 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy310) ≠ (nb078AlphaDummy317) from (by
          unfold
            nb078AlphaDummy317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0308)
                  0)))) (show (nb078AlphaDummy313 g) ≠ (nb078AlphaDummy318 g) from (by
          unfold
            nb078AlphaDummy318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0309
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy310) ≠ (nb078AlphaDummy315)
        from (by
          unfold
            nb078AlphaDummy315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0306)
                  0)))) (show (nb078AlphaDummy313 g) ≠ (nb078AlphaDummy316 g) from (by
          unfold
            nb078AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0307
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy303))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy305 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy311) ≠ (nb078AlphaDummy317)
        from (by
          unfold
            nb078AlphaDummy317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0312)
                  0)))) (show (nb078AlphaDummy314 g) ≠ (nb078AlphaDummy318 g) from (by
          unfold
            nb078AlphaDummy318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0313
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy311) ≠ (nb078AlphaDummy315)
        from (by
          unfold
            nb078AlphaDummy315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0310)
                  0)))) (show (nb078AlphaDummy314 g) ≠ (nb078AlphaDummy316 g) from (by
          unfold
            nb078AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0311
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy310) ≠ (nb078AlphaDummy317) from (by
          unfold
            nb078AlphaDummy317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0308)
                  0)))) (show (nb078AlphaDummy313 g) ≠ (nb078AlphaDummy318 g) from (by
          unfold
            nb078AlphaDummy318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0309
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy310) ≠ (nb078AlphaDummy315)
        from (by
          unfold
            nb078AlphaDummy315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0306)
                  0)))) (show (nb078AlphaDummy313 g) ≠ (nb078AlphaDummy316 g) from (by
          unfold
            nb078AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0307
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy303))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy305 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy311) ≠ (nb078AlphaDummy317)
        from (by
          unfold
            nb078AlphaDummy317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0312)
                  0)))) (show (nb078AlphaDummy314 g) ≠ (nb078AlphaDummy318 g) from (by
          unfold
            nb078AlphaDummy318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0313
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy311) ≠ (nb078AlphaDummy315)
        from (by
          unfold
            nb078AlphaDummy315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0310)
                  0)))) (show (nb078AlphaDummy314 g) ≠ (nb078AlphaDummy316 g) from (by
          unfold
            nb078AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0311
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy311), (nb078AlphaDummy314 g)), ((nb078AlphaDummy310),
        (nb078AlphaDummy313 g)), ((nb078AlphaDummy309), (nb078AlphaDummy312 g)),
        ((nb078AlphaDummy307), (nb078AlphaDummy308 g)), ((nb078AlphaDummy303),
        (nb078AlphaDummy305 g)), ((nb078AlphaDummy304), (nb078AlphaDummy306 g)),
        ((nb078AlphaDummy296), (nb078AlphaDummy298 g)), ((nb078AlphaDummy295),
        (nb078AlphaDummy297 g)), ((nb078AlphaDummy301), (nb078AlphaDummy302 g)),
        ((nb078AlphaDummy299), (nb078AlphaDummy300 g)), ((nb078AlphaDummy288),
        (nb078AlphaDummy291 g)), ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
        ((nb078AlphaDummy293), (nb078AlphaDummy294 g)), ((nb078AlphaDummy285),
        (nb078AlphaDummy286 g)), ((nb078AlphaDummy283), (nb078AlphaDummy284 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy303))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy305 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy303))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy305
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy310) ≠ (nb078AlphaDummy321) from (by
          unfold
            nb078AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0316)
                  0)))) (show (nb078AlphaDummy313 g) ≠ (nb078AlphaDummy322 g) from (by
          unfold
            nb078AlphaDummy322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0317
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy310) ≠ (nb078AlphaDummy319)
        from (by
          unfold
            nb078AlphaDummy319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0314)
                  0)))) (show (nb078AlphaDummy313 g) ≠ (nb078AlphaDummy320 g) from (by
          unfold
            nb078AlphaDummy320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0315
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy303))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy305 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy310) ≠ (nb078AlphaDummy321)
        from (by
          unfold
            nb078AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0316)
                  0)))) (show (nb078AlphaDummy313 g) ≠ (nb078AlphaDummy322 g) from (by
          unfold
            nb078AlphaDummy322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0317
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy310) ≠ (nb078AlphaDummy319)
        from (by
          unfold
            nb078AlphaDummy319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0314)
                  0)))) (show (nb078AlphaDummy313 g) ≠ (nb078AlphaDummy320 g) from (by
          unfold
            nb078AlphaDummy320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0315
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy303))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy305 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy311) ≠ (nb078AlphaDummy323) from (by
          unfold
            nb078AlphaDummy323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0320)
                  0)))) (show (nb078AlphaDummy314 g) ≠ (nb078AlphaDummy324 g) from (by
          unfold
            nb078AlphaDummy324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0321
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy311) ≠ (nb078AlphaDummy319)
        from (by
          unfold
            nb078AlphaDummy319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0318)
                  0)))) (show (nb078AlphaDummy314 g) ≠ (nb078AlphaDummy320 g) from (by
          unfold
            nb078AlphaDummy320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0319
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy311) ≠
        (nb078AlphaDummy323) from (by
          unfold
            nb078AlphaDummy323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0320)
                  0)))) (show (nb078AlphaDummy314 g) ≠ (nb078AlphaDummy324 g) from (by
          unfold
            nb078AlphaDummy324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0321
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy311) ≠ (nb078AlphaDummy319)
        from (by
          unfold
            nb078AlphaDummy319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0318)
                  0)))) (show (nb078AlphaDummy314 g) ≠ (nb078AlphaDummy320 g) from (by
          unfold
            nb078AlphaDummy320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0319
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy303) ≠ (nb078AlphaDummy307) from (by
                                        unfold nb078AlphaDummy307;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0302)
                                                0)))) (show (nb078AlphaDummy305 g) ≠
                                        (nb078AlphaDummy308 g) from (by
                                        unfold nb078AlphaDummy308;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0303 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy307), (nb078AlphaDummy308 g)),
                                    ((nb078AlphaDummy303), (nb078AlphaDummy305 g)),
                                    ((nb078AlphaDummy304), (nb078AlphaDummy306 g)),
                                    ((nb078AlphaDummy296), (nb078AlphaDummy298 g)),
                                    ((nb078AlphaDummy295), (nb078AlphaDummy297 g)),
                                    ((nb078AlphaDummy301), (nb078AlphaDummy302 g)),
                                    ((nb078AlphaDummy299), (nb078AlphaDummy300 g)),
                                    ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
                                    ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
                                    ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
                                    ((nb078AlphaDummy285), (nb078AlphaDummy286 g)),
                                    ((nb078AlphaDummy283), (nb078AlphaDummy284 g)),
                                    ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy303) ≠ (nb078AlphaDummy307) from
                                    (by
                                      unfold nb078AlphaDummy307;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0302)
                                              0)))) (show
                                    (nb078AlphaDummy305 g) ≠ (nb078AlphaDummy308 g) from
                                    (by
                                      unfold nb078AlphaDummy308;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0303 g)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy303) ≠ (nb078AlphaDummy307) from (by
                                        unfold nb078AlphaDummy307;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0302)
                                                0)))) (show (nb078AlphaDummy305 g) ≠
                                        (nb078AlphaDummy308 g) from (by
                                        unfold nb078AlphaDummy308;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0303 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy307), (nb078AlphaDummy308 g)),
                                    ((nb078AlphaDummy303), (nb078AlphaDummy305 g)),
                                    ((nb078AlphaDummy304), (nb078AlphaDummy306 g)),
                                    ((nb078AlphaDummy296), (nb078AlphaDummy298 g)),
                                    ((nb078AlphaDummy295), (nb078AlphaDummy297 g)),
                                    ((nb078AlphaDummy301), (nb078AlphaDummy302 g)),
                                    ((nb078AlphaDummy299), (nb078AlphaDummy300 g)),
                                    ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
                                    ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
                                    ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
                                    ((nb078AlphaDummy285), (nb078AlphaDummy286 g)),
                                    ((nb078AlphaDummy283), (nb078AlphaDummy284 g)),
                                    ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078AlphaDummy287) ≠ (nb078AlphaDummy296) from
                      (by
                        unfold nb078AlphaDummy296;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0294) 1))))
                    (show (nb078AlphaDummy290 g) ≠ (nb078AlphaDummy298 g) from (by
                        unfold nb078AlphaDummy298;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0296 g) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy287) ≠ (nb078AlphaDummy295) from (by
                          unfold nb078AlphaDummy295;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0294) 0))))
                      (show (nb078AlphaDummy290 g) ≠ (nb078AlphaDummy297 g) from (by
                          unfold nb078AlphaDummy297;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0296 g) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy287) ≠ (nb078AlphaDummy301) from (by
                            unfold nb078AlphaDummy301;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0298) 0))))
                        (show (nb078AlphaDummy290 g) ≠ (nb078AlphaDummy302 g) from (by
                            unfold nb078AlphaDummy302;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0299 g) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy287) ≠ (nb078AlphaDummy299) from (by
                              unfold nb078AlphaDummy299;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0295) 0))))
                          (show (nb078AlphaDummy290 g) ≠ (nb078AlphaDummy300 g) from (by
                              unfold nb078AlphaDummy300;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0297 g) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb078AlphaDummy001))).fv ∪
                                ((synCcnv (Class.cv (nb078AlphaDummy001)))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv g)).fv ∪ ((synCcnv (Class.cv g))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078AlphaDummy287))).fv ∪
                        ((Class.cv (nb078AlphaDummy288))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy290 g))).fv ∪
                        ((Class.cv (nb078AlphaDummy291 g))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy296) ≠ (nb078AlphaDummy303) from (by
                                unfold nb078AlphaDummy303;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0300) 0))))
                            (show (nb078AlphaDummy298 g) ≠ (nb078AlphaDummy305 g) from (by
                                unfold nb078AlphaDummy305;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0301 g) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy296) ≠ (nb078AlphaDummy304) from (by
                                  unfold nb078AlphaDummy304;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0300) 1))))
                              (show (nb078AlphaDummy298 g) ≠ (nb078AlphaDummy306 g) from
                                (by
                                  unfold nb078AlphaDummy306;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0301 g) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy296))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy298 g))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy303) ≠ (nb078AlphaDummy310) from (by
          unfold nb078AlphaDummy310;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0304) 1)))) (show (nb078AlphaDummy305 g) ≠
        (nb078AlphaDummy313 g) from (by
          unfold nb078AlphaDummy313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0305 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy303) ≠ (nb078AlphaDummy309) from (by
          unfold nb078AlphaDummy309;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0304) 0)))) (show (nb078AlphaDummy305 g) ≠
        (nb078AlphaDummy312 g) from (by
          unfold nb078AlphaDummy312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0305 g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy303) ≠ (nb078AlphaDummy307)
        from (by
          unfold nb078AlphaDummy307;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0302)
                  0)))) (show (nb078AlphaDummy305 g) ≠ (nb078AlphaDummy308 g) from (by
          unfold nb078AlphaDummy308;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0303 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy311), (nb078AlphaDummy314 g)), ((nb078AlphaDummy310),
        (nb078AlphaDummy313 g)), ((nb078AlphaDummy309), (nb078AlphaDummy312 g)),
        ((nb078AlphaDummy307), (nb078AlphaDummy308 g)), ((nb078AlphaDummy303),
        (nb078AlphaDummy305 g)), ((nb078AlphaDummy304), (nb078AlphaDummy306 g)),
        ((nb078AlphaDummy296), (nb078AlphaDummy298 g)), ((nb078AlphaDummy295),
        (nb078AlphaDummy297 g)), ((nb078AlphaDummy301), (nb078AlphaDummy302 g)),
        ((nb078AlphaDummy299), (nb078AlphaDummy300 g)), ((nb078AlphaDummy288),
        (nb078AlphaDummy291 g)), ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
        ((nb078AlphaDummy293), (nb078AlphaDummy294 g)), ((nb078AlphaDummy285),
        (nb078AlphaDummy286 g)), ((nb078AlphaDummy283), (nb078AlphaDummy284 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy310) ≠ (nb078AlphaDummy317) from (by
          unfold
            nb078AlphaDummy317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0308)
                  0)))) (show (nb078AlphaDummy313 g) ≠ (nb078AlphaDummy318 g) from (by
          unfold
            nb078AlphaDummy318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0309
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy310) ≠ (nb078AlphaDummy315)
        from (by
          unfold
            nb078AlphaDummy315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0306)
                  0)))) (show (nb078AlphaDummy313 g) ≠ (nb078AlphaDummy316 g) from (by
          unfold
            nb078AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0307
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy303))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy305 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy311) ≠ (nb078AlphaDummy317)
        from (by
          unfold
            nb078AlphaDummy317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0312)
                  0)))) (show (nb078AlphaDummy314 g) ≠ (nb078AlphaDummy318 g) from (by
          unfold
            nb078AlphaDummy318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0313
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy311) ≠ (nb078AlphaDummy315)
        from (by
          unfold
            nb078AlphaDummy315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0310)
                  0)))) (show (nb078AlphaDummy314 g) ≠ (nb078AlphaDummy316 g) from (by
          unfold
            nb078AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0311
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy310) ≠ (nb078AlphaDummy317) from (by
          unfold
            nb078AlphaDummy317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0308)
                  0)))) (show (nb078AlphaDummy313 g) ≠ (nb078AlphaDummy318 g) from (by
          unfold
            nb078AlphaDummy318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0309
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy310) ≠ (nb078AlphaDummy315)
        from (by
          unfold
            nb078AlphaDummy315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0306)
                  0)))) (show (nb078AlphaDummy313 g) ≠ (nb078AlphaDummy316 g) from (by
          unfold
            nb078AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0307
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy303))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy305 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy311) ≠ (nb078AlphaDummy317)
        from (by
          unfold
            nb078AlphaDummy317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0312)
                  0)))) (show (nb078AlphaDummy314 g) ≠ (nb078AlphaDummy318 g) from (by
          unfold
            nb078AlphaDummy318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0313
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy311) ≠ (nb078AlphaDummy315)
        from (by
          unfold
            nb078AlphaDummy315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0310)
                  0)))) (show (nb078AlphaDummy314 g) ≠ (nb078AlphaDummy316 g) from (by
          unfold
            nb078AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0311
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy311), (nb078AlphaDummy314 g)), ((nb078AlphaDummy310),
        (nb078AlphaDummy313 g)), ((nb078AlphaDummy309), (nb078AlphaDummy312 g)),
        ((nb078AlphaDummy307), (nb078AlphaDummy308 g)), ((nb078AlphaDummy303),
        (nb078AlphaDummy305 g)), ((nb078AlphaDummy304), (nb078AlphaDummy306 g)),
        ((nb078AlphaDummy296), (nb078AlphaDummy298 g)), ((nb078AlphaDummy295),
        (nb078AlphaDummy297 g)), ((nb078AlphaDummy301), (nb078AlphaDummy302 g)),
        ((nb078AlphaDummy299), (nb078AlphaDummy300 g)), ((nb078AlphaDummy288),
        (nb078AlphaDummy291 g)), ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
        ((nb078AlphaDummy293), (nb078AlphaDummy294 g)), ((nb078AlphaDummy285),
        (nb078AlphaDummy286 g)), ((nb078AlphaDummy283), (nb078AlphaDummy284 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy303))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy305 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy303))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy305
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy310) ≠ (nb078AlphaDummy321) from (by
          unfold
            nb078AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0316)
                  0)))) (show (nb078AlphaDummy313 g) ≠ (nb078AlphaDummy322 g) from (by
          unfold
            nb078AlphaDummy322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0317
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy310) ≠ (nb078AlphaDummy319)
        from (by
          unfold
            nb078AlphaDummy319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0314)
                  0)))) (show (nb078AlphaDummy313 g) ≠ (nb078AlphaDummy320 g) from (by
          unfold
            nb078AlphaDummy320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0315
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy303))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy305 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy310) ≠ (nb078AlphaDummy321)
        from (by
          unfold
            nb078AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0316)
                  0)))) (show (nb078AlphaDummy313 g) ≠ (nb078AlphaDummy322 g) from (by
          unfold
            nb078AlphaDummy322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0317
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy310) ≠ (nb078AlphaDummy319)
        from (by
          unfold
            nb078AlphaDummy319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0314)
                  0)))) (show (nb078AlphaDummy313 g) ≠ (nb078AlphaDummy320 g) from (by
          unfold
            nb078AlphaDummy320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0315
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy303))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy305 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy311) ≠ (nb078AlphaDummy323) from (by
          unfold
            nb078AlphaDummy323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0320)
                  0)))) (show (nb078AlphaDummy314 g) ≠ (nb078AlphaDummy324 g) from (by
          unfold
            nb078AlphaDummy324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0321
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy311) ≠ (nb078AlphaDummy319)
        from (by
          unfold
            nb078AlphaDummy319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0318)
                  0)))) (show (nb078AlphaDummy314 g) ≠ (nb078AlphaDummy320 g) from (by
          unfold
            nb078AlphaDummy320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0319
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy311) ≠
        (nb078AlphaDummy323) from (by
          unfold
            nb078AlphaDummy323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0320)
                  0)))) (show (nb078AlphaDummy314 g) ≠ (nb078AlphaDummy324 g) from (by
          unfold
            nb078AlphaDummy324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0321
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy311) ≠ (nb078AlphaDummy319)
        from (by
          unfold
            nb078AlphaDummy319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0318)
                  0)))) (show (nb078AlphaDummy314 g) ≠ (nb078AlphaDummy320 g) from (by
          unfold
            nb078AlphaDummy320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0319
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy303) ≠ (nb078AlphaDummy307) from
                                        (by
                                          unfold nb078AlphaDummy307;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0302)
                                                  0)))) (show (nb078AlphaDummy305 g) ≠
        (nb078AlphaDummy308 g) from (by
                                          unfold nb078AlphaDummy308;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0303 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy307), (nb078AlphaDummy308 g)),
                                      ((nb078AlphaDummy303), (nb078AlphaDummy305 g)),
                                      ((nb078AlphaDummy304), (nb078AlphaDummy306 g)),
                                      ((nb078AlphaDummy296), (nb078AlphaDummy298 g)),
                                      ((nb078AlphaDummy295), (nb078AlphaDummy297 g)),
                                      ((nb078AlphaDummy301), (nb078AlphaDummy302 g)),
                                      ((nb078AlphaDummy299), (nb078AlphaDummy300 g)),
                                      ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
                                      ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
                                      ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
                                      ((nb078AlphaDummy285), (nb078AlphaDummy286 g)),
                                      ((nb078AlphaDummy283), (nb078AlphaDummy284 g)),
                                      ((nb078AlphaDummy001), g),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy303) ≠ (nb078AlphaDummy307) from (by
                                        unfold nb078AlphaDummy307;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0302)
                                                0)))) (show (nb078AlphaDummy305 g) ≠
                                        (nb078AlphaDummy308 g) from (by
                                        unfold nb078AlphaDummy308;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0303 g)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy303) ≠ (nb078AlphaDummy307) from
                                        (by
                                          unfold nb078AlphaDummy307;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0302)
                                                  0)))) (show (nb078AlphaDummy305 g) ≠
        (nb078AlphaDummy308 g) from (by
                                          unfold nb078AlphaDummy308;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0303 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy307), (nb078AlphaDummy308 g)),
                                      ((nb078AlphaDummy303), (nb078AlphaDummy305 g)),
                                      ((nb078AlphaDummy304), (nb078AlphaDummy306 g)),
                                      ((nb078AlphaDummy296), (nb078AlphaDummy298 g)),
                                      ((nb078AlphaDummy295), (nb078AlphaDummy297 g)),
                                      ((nb078AlphaDummy301), (nb078AlphaDummy302 g)),
                                      ((nb078AlphaDummy299), (nb078AlphaDummy300 g)),
                                      ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
                                      ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
                                      ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
                                      ((nb078AlphaDummy285), (nb078AlphaDummy286 g)),
                                      ((nb078AlphaDummy283), (nb078AlphaDummy284 g)),
                                      ((nb078AlphaDummy001), g),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part061`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0031`. -/
@[expose]
noncomputable def nb078SplitAlpha0031 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078AlphaDummy327), (nb078AlphaDummy328 g)),
        ((nb078AlphaDummy296), (nb078AlphaDummy298 g)),
        ((nb078AlphaDummy295), (nb078AlphaDummy297 g)),
        ((nb078AlphaDummy325), (nb078AlphaDummy326 g)),
        ((nb078AlphaDummy299), (nb078AlphaDummy300 g)),
        ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
        ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
        ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
        ((nb078AlphaDummy285), (nb078AlphaDummy286 g)),
        ((nb078AlphaDummy283), (nb078AlphaDummy284 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy327))
          (synCcompl (synCphi (Class.cv (nb078AlphaDummy296))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy327)) (synCcompl (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy328 g))
          (synCcompl (synCphi (Class.cv (nb078AlphaDummy298 g))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy328 g))
            (synCcompl (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy296) ≠ (nb078AlphaDummy303) from (by
                              unfold nb078AlphaDummy303;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0300) 0))))
                          (show (nb078AlphaDummy298 g) ≠ (nb078AlphaDummy305 g) from (by
                              unfold nb078AlphaDummy305;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0301 g) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy296) ≠ (nb078AlphaDummy304) from (by
                                unfold nb078AlphaDummy304;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0300) 1))))
                            (show (nb078AlphaDummy298 g) ≠ (nb078AlphaDummy306 g) from (by
                                unfold nb078AlphaDummy306;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0301 g) 1))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy296) ≠ (nb078AlphaDummy329) from (by
                                  unfold nb078AlphaDummy329;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0330) 0))))
                              (show (nb078AlphaDummy298 g) ≠ (nb078AlphaDummy330 g) from
                                (by
                                  unfold nb078AlphaDummy330;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0331 g) 0))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy296) ≠ (nb078AlphaDummy327) from (by
                                    unfold nb078AlphaDummy327;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0328) 0)))) (show
                                  (nb078AlphaDummy298 g) ≠ (nb078AlphaDummy328 g) from (by
                                    unfold nb078AlphaDummy328;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0329 g)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy296))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy298 g))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy303) ≠ (nb078AlphaDummy310) from (by
          unfold nb078AlphaDummy310;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0304) 1)))) (show (nb078AlphaDummy305 g) ≠
        (nb078AlphaDummy313 g) from (by
          unfold nb078AlphaDummy313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0305 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy303) ≠ (nb078AlphaDummy309) from (by
          unfold nb078AlphaDummy309;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0304) 0)))) (show (nb078AlphaDummy305 g) ≠
        (nb078AlphaDummy312 g) from (by
          unfold nb078AlphaDummy312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0305 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy303) ≠ (nb078AlphaDummy307) from (by
          unfold nb078AlphaDummy307;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0302) 0)))) (show (nb078AlphaDummy305 g) ≠
        (nb078AlphaDummy308 g) from (by
          unfold nb078AlphaDummy308;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0303 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy311), (nb078AlphaDummy314 g)), ((nb078AlphaDummy310),
        (nb078AlphaDummy313 g)), ((nb078AlphaDummy309), (nb078AlphaDummy312 g)),
        ((nb078AlphaDummy307), (nb078AlphaDummy308 g)), ((nb078AlphaDummy303),
        (nb078AlphaDummy305 g)), ((nb078AlphaDummy304), (nb078AlphaDummy306 g)),
        ((nb078AlphaDummy329), (nb078AlphaDummy330 g)), ((nb078AlphaDummy327),
        (nb078AlphaDummy328 g)), ((nb078AlphaDummy296), (nb078AlphaDummy298 g)),
        ((nb078AlphaDummy295), (nb078AlphaDummy297 g)), ((nb078AlphaDummy325),
        (nb078AlphaDummy326 g)), ((nb078AlphaDummy299), (nb078AlphaDummy300 g)),
        ((nb078AlphaDummy288), (nb078AlphaDummy291 g)), ((nb078AlphaDummy287),
        (nb078AlphaDummy290 g)), ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
        ((nb078AlphaDummy285), (nb078AlphaDummy286 g)), ((nb078AlphaDummy283),
        (nb078AlphaDummy284 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy310) ≠ (nb078AlphaDummy317) from (by
          unfold
            nb078AlphaDummy317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0308)
                  0)))) (show (nb078AlphaDummy313 g) ≠ (nb078AlphaDummy318 g) from (by
          unfold
            nb078AlphaDummy318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0309
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy310) ≠ (nb078AlphaDummy315)
        from (by
          unfold
            nb078AlphaDummy315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0306)
                  0)))) (show (nb078AlphaDummy313 g) ≠ (nb078AlphaDummy316 g) from (by
          unfold
            nb078AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0307
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy303))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy305 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy311) ≠ (nb078AlphaDummy317)
        from (by
          unfold
            nb078AlphaDummy317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0312)
                  0)))) (show (nb078AlphaDummy314 g) ≠ (nb078AlphaDummy318 g) from (by
          unfold
            nb078AlphaDummy318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0313
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy311) ≠ (nb078AlphaDummy315)
        from (by
          unfold
            nb078AlphaDummy315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0310)
                  0)))) (show (nb078AlphaDummy314 g) ≠ (nb078AlphaDummy316 g) from (by
          unfold
            nb078AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0311
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy310) ≠ (nb078AlphaDummy317) from (by
          unfold
            nb078AlphaDummy317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0308)
                  0)))) (show (nb078AlphaDummy313 g) ≠ (nb078AlphaDummy318 g) from (by
          unfold
            nb078AlphaDummy318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0309
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy310) ≠ (nb078AlphaDummy315)
        from (by
          unfold
            nb078AlphaDummy315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0306)
                  0)))) (show (nb078AlphaDummy313 g) ≠ (nb078AlphaDummy316 g) from (by
          unfold
            nb078AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0307
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy303))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy305 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy311) ≠ (nb078AlphaDummy317)
        from (by
          unfold
            nb078AlphaDummy317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0312)
                  0)))) (show (nb078AlphaDummy314 g) ≠ (nb078AlphaDummy318 g) from (by
          unfold
            nb078AlphaDummy318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0313
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy311) ≠ (nb078AlphaDummy315)
        from (by
          unfold
            nb078AlphaDummy315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0310)
                  0)))) (show (nb078AlphaDummy314 g) ≠ (nb078AlphaDummy316 g) from (by
          unfold
            nb078AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0311
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy311), (nb078AlphaDummy314 g)), ((nb078AlphaDummy310),
        (nb078AlphaDummy313 g)), ((nb078AlphaDummy309), (nb078AlphaDummy312 g)),
        ((nb078AlphaDummy307), (nb078AlphaDummy308 g)), ((nb078AlphaDummy303),
        (nb078AlphaDummy305 g)), ((nb078AlphaDummy304), (nb078AlphaDummy306 g)),
        ((nb078AlphaDummy329), (nb078AlphaDummy330 g)), ((nb078AlphaDummy327),
        (nb078AlphaDummy328 g)), ((nb078AlphaDummy296), (nb078AlphaDummy298 g)),
        ((nb078AlphaDummy295), (nb078AlphaDummy297 g)), ((nb078AlphaDummy325),
        (nb078AlphaDummy326 g)), ((nb078AlphaDummy299), (nb078AlphaDummy300 g)),
        ((nb078AlphaDummy288), (nb078AlphaDummy291 g)), ((nb078AlphaDummy287),
        (nb078AlphaDummy290 g)), ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
        ((nb078AlphaDummy285), (nb078AlphaDummy286 g)), ((nb078AlphaDummy283),
        (nb078AlphaDummy284 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy303))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy305 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy303))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy305
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy310) ≠ (nb078AlphaDummy321) from (by
          unfold
            nb078AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0316)
                  0)))) (show (nb078AlphaDummy313 g) ≠ (nb078AlphaDummy322 g) from (by
          unfold
            nb078AlphaDummy322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0317
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy310) ≠ (nb078AlphaDummy319)
        from (by
          unfold
            nb078AlphaDummy319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0314)
                  0)))) (show (nb078AlphaDummy313 g) ≠ (nb078AlphaDummy320 g) from (by
          unfold
            nb078AlphaDummy320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0315
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy303))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy305 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy310) ≠ (nb078AlphaDummy321)
        from (by
          unfold
            nb078AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0316)
                  0)))) (show (nb078AlphaDummy313 g) ≠ (nb078AlphaDummy322 g) from (by
          unfold
            nb078AlphaDummy322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0317
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy310) ≠ (nb078AlphaDummy319)
        from (by
          unfold
            nb078AlphaDummy319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0314)
                  0)))) (show (nb078AlphaDummy313 g) ≠ (nb078AlphaDummy320 g) from (by
          unfold
            nb078AlphaDummy320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0315
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy303))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy305 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy311) ≠ (nb078AlphaDummy323) from (by
          unfold
            nb078AlphaDummy323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0320)
                  0)))) (show (nb078AlphaDummy314 g) ≠ (nb078AlphaDummy324 g) from (by
          unfold
            nb078AlphaDummy324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0321
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy311) ≠ (nb078AlphaDummy319)
        from (by
          unfold
            nb078AlphaDummy319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0318)
                  0)))) (show (nb078AlphaDummy314 g) ≠ (nb078AlphaDummy320 g) from (by
          unfold
            nb078AlphaDummy320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0319
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy311) ≠
        (nb078AlphaDummy323) from (by
          unfold
            nb078AlphaDummy323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0320)
                  0)))) (show (nb078AlphaDummy314 g) ≠ (nb078AlphaDummy324 g) from (by
          unfold
            nb078AlphaDummy324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0321
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy311) ≠ (nb078AlphaDummy319)
        from (by
          unfold
            nb078AlphaDummy319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0318)
                  0)))) (show (nb078AlphaDummy314 g) ≠ (nb078AlphaDummy320 g) from (by
          unfold
            nb078AlphaDummy320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0319
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy303) ≠ (nb078AlphaDummy307) from (by
                                        unfold nb078AlphaDummy307;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0302)
                                                0)))) (show (nb078AlphaDummy305 g) ≠
                                        (nb078AlphaDummy308 g) from (by
                                        unfold nb078AlphaDummy308;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0303 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy307), (nb078AlphaDummy308 g)),
                                    ((nb078AlphaDummy303), (nb078AlphaDummy305 g)),
                                    ((nb078AlphaDummy304), (nb078AlphaDummy306 g)),
                                    ((nb078AlphaDummy329), (nb078AlphaDummy330 g)),
                                    ((nb078AlphaDummy327), (nb078AlphaDummy328 g)),
                                    ((nb078AlphaDummy296), (nb078AlphaDummy298 g)),
                                    ((nb078AlphaDummy295), (nb078AlphaDummy297 g)),
                                    ((nb078AlphaDummy325), (nb078AlphaDummy326 g)),
                                    ((nb078AlphaDummy299), (nb078AlphaDummy300 g)),
                                    ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
                                    ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
                                    ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
                                    ((nb078AlphaDummy285), (nb078AlphaDummy286 g)),
                                    ((nb078AlphaDummy283), (nb078AlphaDummy284 g)),
                                    ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy303) ≠ (nb078AlphaDummy307) from
                                    (by
                                      unfold nb078AlphaDummy307;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0302)
                                              0)))) (show
                                    (nb078AlphaDummy305 g) ≠ (nb078AlphaDummy308 g) from
                                    (by
                                      unfold nb078AlphaDummy308;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0303 g)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy303) ≠ (nb078AlphaDummy307) from (by
                                        unfold nb078AlphaDummy307;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0302)
                                                0)))) (show (nb078AlphaDummy305 g) ≠
                                        (nb078AlphaDummy308 g) from (by
                                        unfold nb078AlphaDummy308;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0303 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy307), (nb078AlphaDummy308 g)),
                                    ((nb078AlphaDummy303), (nb078AlphaDummy305 g)),
                                    ((nb078AlphaDummy304), (nb078AlphaDummy306 g)),
                                    ((nb078AlphaDummy329), (nb078AlphaDummy330 g)),
                                    ((nb078AlphaDummy327), (nb078AlphaDummy328 g)),
                                    ((nb078AlphaDummy296), (nb078AlphaDummy298 g)),
                                    ((nb078AlphaDummy295), (nb078AlphaDummy297 g)),
                                    ((nb078AlphaDummy325), (nb078AlphaDummy326 g)),
                                    ((nb078AlphaDummy299), (nb078AlphaDummy300 g)),
                                    ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
                                    ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
                                    ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
                                    ((nb078AlphaDummy285), (nb078AlphaDummy286 g)),
                                    ((nb078AlphaDummy283), (nb078AlphaDummy284 g)),
                                    ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy296) ≠ (nb078AlphaDummy303) from (by
                              unfold nb078AlphaDummy303;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0300) 0))))
                          (show (nb078AlphaDummy298 g) ≠ (nb078AlphaDummy305 g) from (by
                              unfold nb078AlphaDummy305;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0301 g) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy296) ≠ (nb078AlphaDummy304) from (by
                                unfold nb078AlphaDummy304;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0300) 1))))
                            (show (nb078AlphaDummy298 g) ≠ (nb078AlphaDummy306 g) from (by
                                unfold nb078AlphaDummy306;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0301 g) 1))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy296) ≠ (nb078AlphaDummy329) from (by
                                  unfold nb078AlphaDummy329;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0330) 0))))
                              (show (nb078AlphaDummy298 g) ≠ (nb078AlphaDummy330 g) from
                                (by
                                  unfold nb078AlphaDummy330;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0331 g) 0))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy296) ≠ (nb078AlphaDummy327) from (by
                                    unfold nb078AlphaDummy327;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0328) 0)))) (show
                                  (nb078AlphaDummy298 g) ≠ (nb078AlphaDummy328 g) from (by
                                    unfold nb078AlphaDummy328;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0329 g)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy296))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy298 g))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy303) ≠ (nb078AlphaDummy310) from (by
          unfold nb078AlphaDummy310;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0304) 1)))) (show (nb078AlphaDummy305 g) ≠
        (nb078AlphaDummy313 g) from (by
          unfold nb078AlphaDummy313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0305 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy303) ≠ (nb078AlphaDummy309) from (by
          unfold nb078AlphaDummy309;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0304) 0)))) (show (nb078AlphaDummy305 g) ≠
        (nb078AlphaDummy312 g) from (by
          unfold nb078AlphaDummy312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0305 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy303) ≠ (nb078AlphaDummy307) from (by
          unfold nb078AlphaDummy307;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0302) 0)))) (show (nb078AlphaDummy305 g) ≠
        (nb078AlphaDummy308 g) from (by
          unfold nb078AlphaDummy308;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0303 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy311), (nb078AlphaDummy314 g)), ((nb078AlphaDummy310),
        (nb078AlphaDummy313 g)), ((nb078AlphaDummy309), (nb078AlphaDummy312 g)),
        ((nb078AlphaDummy307), (nb078AlphaDummy308 g)), ((nb078AlphaDummy303),
        (nb078AlphaDummy305 g)), ((nb078AlphaDummy304), (nb078AlphaDummy306 g)),
        ((nb078AlphaDummy329), (nb078AlphaDummy330 g)), ((nb078AlphaDummy327),
        (nb078AlphaDummy328 g)), ((nb078AlphaDummy296), (nb078AlphaDummy298 g)),
        ((nb078AlphaDummy295), (nb078AlphaDummy297 g)), ((nb078AlphaDummy325),
        (nb078AlphaDummy326 g)), ((nb078AlphaDummy299), (nb078AlphaDummy300 g)),
        ((nb078AlphaDummy288), (nb078AlphaDummy291 g)), ((nb078AlphaDummy287),
        (nb078AlphaDummy290 g)), ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
        ((nb078AlphaDummy285), (nb078AlphaDummy286 g)), ((nb078AlphaDummy283),
        (nb078AlphaDummy284 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy310) ≠ (nb078AlphaDummy317) from (by
          unfold
            nb078AlphaDummy317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0308)
                  0)))) (show (nb078AlphaDummy313 g) ≠ (nb078AlphaDummy318 g) from (by
          unfold
            nb078AlphaDummy318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0309
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy310) ≠ (nb078AlphaDummy315)
        from (by
          unfold
            nb078AlphaDummy315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0306)
                  0)))) (show (nb078AlphaDummy313 g) ≠ (nb078AlphaDummy316 g) from (by
          unfold
            nb078AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0307
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy303))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy305 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy311) ≠ (nb078AlphaDummy317)
        from (by
          unfold
            nb078AlphaDummy317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0312)
                  0)))) (show (nb078AlphaDummy314 g) ≠ (nb078AlphaDummy318 g) from (by
          unfold
            nb078AlphaDummy318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0313
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy311) ≠ (nb078AlphaDummy315)
        from (by
          unfold
            nb078AlphaDummy315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0310)
                  0)))) (show (nb078AlphaDummy314 g) ≠ (nb078AlphaDummy316 g) from (by
          unfold
            nb078AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0311
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy310) ≠ (nb078AlphaDummy317) from (by
          unfold
            nb078AlphaDummy317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0308)
                  0)))) (show (nb078AlphaDummy313 g) ≠ (nb078AlphaDummy318 g) from (by
          unfold
            nb078AlphaDummy318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0309
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy310) ≠ (nb078AlphaDummy315)
        from (by
          unfold
            nb078AlphaDummy315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0306)
                  0)))) (show (nb078AlphaDummy313 g) ≠ (nb078AlphaDummy316 g) from (by
          unfold
            nb078AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0307
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy303))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy305 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy311) ≠ (nb078AlphaDummy317)
        from (by
          unfold
            nb078AlphaDummy317;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0312)
                  0)))) (show (nb078AlphaDummy314 g) ≠ (nb078AlphaDummy318 g) from (by
          unfold
            nb078AlphaDummy318;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0313
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy311) ≠ (nb078AlphaDummy315)
        from (by
          unfold
            nb078AlphaDummy315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0310)
                  0)))) (show (nb078AlphaDummy314 g) ≠ (nb078AlphaDummy316 g) from (by
          unfold
            nb078AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0311
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy311), (nb078AlphaDummy314 g)), ((nb078AlphaDummy310),
        (nb078AlphaDummy313 g)), ((nb078AlphaDummy309), (nb078AlphaDummy312 g)),
        ((nb078AlphaDummy307), (nb078AlphaDummy308 g)), ((nb078AlphaDummy303),
        (nb078AlphaDummy305 g)), ((nb078AlphaDummy304), (nb078AlphaDummy306 g)),
        ((nb078AlphaDummy329), (nb078AlphaDummy330 g)), ((nb078AlphaDummy327),
        (nb078AlphaDummy328 g)), ((nb078AlphaDummy296), (nb078AlphaDummy298 g)),
        ((nb078AlphaDummy295), (nb078AlphaDummy297 g)), ((nb078AlphaDummy325),
        (nb078AlphaDummy326 g)), ((nb078AlphaDummy299), (nb078AlphaDummy300 g)),
        ((nb078AlphaDummy288), (nb078AlphaDummy291 g)), ((nb078AlphaDummy287),
        (nb078AlphaDummy290 g)), ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
        ((nb078AlphaDummy285), (nb078AlphaDummy286 g)), ((nb078AlphaDummy283),
        (nb078AlphaDummy284 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy303))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy305 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy303))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy305
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy310) ≠ (nb078AlphaDummy321) from (by
          unfold
            nb078AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0316)
                  0)))) (show (nb078AlphaDummy313 g) ≠ (nb078AlphaDummy322 g) from (by
          unfold
            nb078AlphaDummy322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0317
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy310) ≠ (nb078AlphaDummy319)
        from (by
          unfold
            nb078AlphaDummy319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0314)
                  0)))) (show (nb078AlphaDummy313 g) ≠ (nb078AlphaDummy320 g) from (by
          unfold
            nb078AlphaDummy320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0315
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy303))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy305 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy310) ≠ (nb078AlphaDummy321)
        from (by
          unfold
            nb078AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0316)
                  0)))) (show (nb078AlphaDummy313 g) ≠ (nb078AlphaDummy322 g) from (by
          unfold
            nb078AlphaDummy322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0317
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy310) ≠ (nb078AlphaDummy319)
        from (by
          unfold
            nb078AlphaDummy319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0314)
                  0)))) (show (nb078AlphaDummy313 g) ≠ (nb078AlphaDummy320 g) from (by
          unfold
            nb078AlphaDummy320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0315
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy303))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy305 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy311) ≠ (nb078AlphaDummy323) from (by
          unfold
            nb078AlphaDummy323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0320)
                  0)))) (show (nb078AlphaDummy314 g) ≠ (nb078AlphaDummy324 g) from (by
          unfold
            nb078AlphaDummy324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0321
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy311) ≠ (nb078AlphaDummy319)
        from (by
          unfold
            nb078AlphaDummy319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0318)
                  0)))) (show (nb078AlphaDummy314 g) ≠ (nb078AlphaDummy320 g) from (by
          unfold
            nb078AlphaDummy320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0319
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy311) ≠
        (nb078AlphaDummy323) from (by
          unfold
            nb078AlphaDummy323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0320)
                  0)))) (show (nb078AlphaDummy314 g) ≠ (nb078AlphaDummy324 g) from (by
          unfold
            nb078AlphaDummy324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0321
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy311) ≠ (nb078AlphaDummy319)
        from (by
          unfold
            nb078AlphaDummy319;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0318)
                  0)))) (show (nb078AlphaDummy314 g) ≠ (nb078AlphaDummy320 g) from (by
          unfold
            nb078AlphaDummy320;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0319
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy303) ≠ (nb078AlphaDummy307) from (by
                                        unfold nb078AlphaDummy307;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0302)
                                                0)))) (show (nb078AlphaDummy305 g) ≠
                                        (nb078AlphaDummy308 g) from (by
                                        unfold nb078AlphaDummy308;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0303 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy307), (nb078AlphaDummy308 g)),
                                    ((nb078AlphaDummy303), (nb078AlphaDummy305 g)),
                                    ((nb078AlphaDummy304), (nb078AlphaDummy306 g)),
                                    ((nb078AlphaDummy329), (nb078AlphaDummy330 g)),
                                    ((nb078AlphaDummy327), (nb078AlphaDummy328 g)),
                                    ((nb078AlphaDummy296), (nb078AlphaDummy298 g)),
                                    ((nb078AlphaDummy295), (nb078AlphaDummy297 g)),
                                    ((nb078AlphaDummy325), (nb078AlphaDummy326 g)),
                                    ((nb078AlphaDummy299), (nb078AlphaDummy300 g)),
                                    ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
                                    ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
                                    ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
                                    ((nb078AlphaDummy285), (nb078AlphaDummy286 g)),
                                    ((nb078AlphaDummy283), (nb078AlphaDummy284 g)),
                                    ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy303) ≠ (nb078AlphaDummy307) from
                                    (by
                                      unfold nb078AlphaDummy307;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0302)
                                              0)))) (show
                                    (nb078AlphaDummy305 g) ≠ (nb078AlphaDummy308 g) from
                                    (by
                                      unfold nb078AlphaDummy308;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0303 g)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy303) ≠ (nb078AlphaDummy307) from (by
                                        unfold nb078AlphaDummy307;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0302)
                                                0)))) (show (nb078AlphaDummy305 g) ≠
                                        (nb078AlphaDummy308 g) from (by
                                        unfold nb078AlphaDummy308;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0303 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy307), (nb078AlphaDummy308 g)),
                                    ((nb078AlphaDummy303), (nb078AlphaDummy305 g)),
                                    ((nb078AlphaDummy304), (nb078AlphaDummy306 g)),
                                    ((nb078AlphaDummy329), (nb078AlphaDummy330 g)),
                                    ((nb078AlphaDummy327), (nb078AlphaDummy328 g)),
                                    ((nb078AlphaDummy296), (nb078AlphaDummy298 g)),
                                    ((nb078AlphaDummy295), (nb078AlphaDummy297 g)),
                                    ((nb078AlphaDummy325), (nb078AlphaDummy326 g)),
                                    ((nb078AlphaDummy299), (nb078AlphaDummy300 g)),
                                    ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
                                    ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
                                    ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
                                    ((nb078AlphaDummy285), (nb078AlphaDummy286 g)),
                                    ((nb078AlphaDummy283), (nb078AlphaDummy284 g)),
                                    ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.reflOfClosed [((nb078AlphaDummy327), (nb078AlphaDummy328 g)),
            ((nb078AlphaDummy296), (nb078AlphaDummy298 g)),
            ((nb078AlphaDummy295), (nb078AlphaDummy297 g)),
            ((nb078AlphaDummy325), (nb078AlphaDummy326 g)),
            ((nb078AlphaDummy299), (nb078AlphaDummy300 g)),
            ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
            ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
            ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
            ((nb078AlphaDummy285), (nb078AlphaDummy286 g)),
            ((nb078AlphaDummy283), (nb078AlphaDummy284 g)),
            ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
            ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part062`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0032`. -/
@[expose]
noncomputable def nb078SplitAlpha0032 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078AlphaDummy337), (nb078AlphaDummy338 g)),
        ((nb078AlphaDummy335), (nb078AlphaDummy336 g)),
        ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
        ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
        ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
        ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
        ((nb078AlphaDummy285), (nb078AlphaDummy286 g)),
        ((nb078AlphaDummy283), (nb078AlphaDummy284 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy337))
          (Class.cab (nb078AlphaDummy331)
            (synWrex (nb078AlphaDummy332) (Class.cv (nb078AlphaDummy287))
              (Wff.classEq (Class.cv (nb078AlphaDummy331))
                (synCphi (Class.cv (nb078AlphaDummy332))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy337)) (Class.cab (nb078AlphaDummy331)
              (synWrex (nb078AlphaDummy332) (Class.cv (nb078AlphaDummy287))
                (Wff.classEq (Class.cv (nb078AlphaDummy331))
                  (synCphi (Class.cv (nb078AlphaDummy332)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy338 g))
          (Class.cab (nb078AlphaDummy333 g)
            (synWrex (nb078AlphaDummy334 g) (Class.cv (nb078AlphaDummy290 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy333 g))
                (synCphi (Class.cv (nb078AlphaDummy334 g))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy338 g))
            (Class.cab (nb078AlphaDummy333 g)
              (synWrex (nb078AlphaDummy334 g) (Class.cv (nb078AlphaDummy290 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy333 g))
                  (synCphi (Class.cv (nb078AlphaDummy334 g))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy287) ≠ (nb078AlphaDummy332) from
                    (by
                      unfold nb078AlphaDummy332;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0332) 1))))
                  (show (nb078AlphaDummy290 g) ≠ (nb078AlphaDummy334 g) from (by
                      unfold nb078AlphaDummy334;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0334 g) 1))))
                  (TAlphaVar.there (show (nb078AlphaDummy287) ≠ (nb078AlphaDummy331) from
                      (by
                        unfold nb078AlphaDummy331;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0332) 0))))
                    (show (nb078AlphaDummy290 g) ≠ (nb078AlphaDummy333 g) from (by
                        unfold nb078AlphaDummy333;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0334 g) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy287) ≠ (nb078AlphaDummy337) from (by
                          unfold nb078AlphaDummy337;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0336) 0))))
                      (show (nb078AlphaDummy290 g) ≠ (nb078AlphaDummy338 g) from (by
                          unfold nb078AlphaDummy338;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0337 g) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy287) ≠ (nb078AlphaDummy335) from (by
                            unfold nb078AlphaDummy335;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0333) 0))))
                        (show (nb078AlphaDummy290 g) ≠ (nb078AlphaDummy336 g) from (by
                            unfold nb078AlphaDummy336;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0335 g) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb078AlphaDummy001))).fv ∪
                              ((synCcnv (Class.cv (nb078AlphaDummy001)))).fv) (by decide))
                          (freshVar_injective (((Class.cv g)).fv ∪ ((synCcnv (Class.cv g))).fv)
                            (by decide)) (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb078AlphaDummy001))).fv ∪
                                ((synCcnv (Class.cv (nb078AlphaDummy001)))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv g)).fv ∪ ((synCcnv (Class.cv g))).fv) (by decide))
                            (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy287))).fv ∪
                      ((Class.cv (nb078AlphaDummy289))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078AlphaDummy290 g))).fv ∪
                      ((Class.cv (nb078AlphaDummy292 g))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy332) ≠ (nb078AlphaDummy339) from (by
                              unfold nb078AlphaDummy339;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0338) 0))))
                          (show (nb078AlphaDummy334 g) ≠ (nb078AlphaDummy341 g) from (by
                              unfold nb078AlphaDummy341;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0339 g) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy332) ≠ (nb078AlphaDummy340) from (by
                                unfold nb078AlphaDummy340;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0338) 1))))
                            (show (nb078AlphaDummy334 g) ≠ (nb078AlphaDummy342 g) from (by
                                unfold nb078AlphaDummy342;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0339 g) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy332))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy334 g))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy339) ≠ (nb078AlphaDummy346) from (by
          unfold nb078AlphaDummy346;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0342) 1)))) (show (nb078AlphaDummy341 g) ≠
        (nb078AlphaDummy349 g) from (by
          unfold nb078AlphaDummy349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0343 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy339) ≠ (nb078AlphaDummy345) from (by
          unfold nb078AlphaDummy345;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0342) 0)))) (show (nb078AlphaDummy341 g) ≠
        (nb078AlphaDummy348 g) from (by
          unfold nb078AlphaDummy348;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0343 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy339) ≠ (nb078AlphaDummy343) from (by
          unfold nb078AlphaDummy343;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0340) 0)))) (show (nb078AlphaDummy341 g) ≠
        (nb078AlphaDummy344 g) from (by
          unfold nb078AlphaDummy344;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0341 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy347), (nb078AlphaDummy350 g)), ((nb078AlphaDummy346),
        (nb078AlphaDummy349 g)), ((nb078AlphaDummy345), (nb078AlphaDummy348 g)),
        ((nb078AlphaDummy343), (nb078AlphaDummy344 g)), ((nb078AlphaDummy339),
        (nb078AlphaDummy341 g)), ((nb078AlphaDummy340), (nb078AlphaDummy342 g)),
        ((nb078AlphaDummy332), (nb078AlphaDummy334 g)), ((nb078AlphaDummy331),
        (nb078AlphaDummy333 g)), ((nb078AlphaDummy337), (nb078AlphaDummy338 g)),
        ((nb078AlphaDummy335), (nb078AlphaDummy336 g)), ((nb078AlphaDummy289),
        (nb078AlphaDummy292 g)), ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
        ((nb078AlphaDummy287), (nb078AlphaDummy290 g)), ((nb078AlphaDummy293),
        (nb078AlphaDummy294 g)), ((nb078AlphaDummy285), (nb078AlphaDummy286 g)),
        ((nb078AlphaDummy283), (nb078AlphaDummy284 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy346) ≠ (nb078AlphaDummy353) from (by
          unfold
            nb078AlphaDummy353;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0346)
                  0)))) (show (nb078AlphaDummy349 g) ≠ (nb078AlphaDummy354 g) from (by
          unfold
            nb078AlphaDummy354;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0347
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy346) ≠ (nb078AlphaDummy351)
        from (by
          unfold
            nb078AlphaDummy351;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0344)
                  0)))) (show (nb078AlphaDummy349 g) ≠ (nb078AlphaDummy352 g) from (by
          unfold
            nb078AlphaDummy352;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0345
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy339))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy341 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy347) ≠ (nb078AlphaDummy353)
        from (by
          unfold
            nb078AlphaDummy353;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0350)
                  0)))) (show (nb078AlphaDummy350 g) ≠ (nb078AlphaDummy354 g) from (by
          unfold
            nb078AlphaDummy354;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0351
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy347) ≠ (nb078AlphaDummy351)
        from (by
          unfold
            nb078AlphaDummy351;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0348)
                  0)))) (show (nb078AlphaDummy350 g) ≠ (nb078AlphaDummy352 g) from (by
          unfold
            nb078AlphaDummy352;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0349
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy346) ≠ (nb078AlphaDummy353) from (by
          unfold
            nb078AlphaDummy353;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0346)
                  0)))) (show (nb078AlphaDummy349 g) ≠ (nb078AlphaDummy354 g) from (by
          unfold
            nb078AlphaDummy354;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0347
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy346) ≠ (nb078AlphaDummy351)
        from (by
          unfold
            nb078AlphaDummy351;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0344)
                  0)))) (show (nb078AlphaDummy349 g) ≠ (nb078AlphaDummy352 g) from (by
          unfold
            nb078AlphaDummy352;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0345
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy339))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy341 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy347) ≠ (nb078AlphaDummy353)
        from (by
          unfold
            nb078AlphaDummy353;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0350)
                  0)))) (show (nb078AlphaDummy350 g) ≠ (nb078AlphaDummy354 g) from (by
          unfold
            nb078AlphaDummy354;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0351
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy347) ≠ (nb078AlphaDummy351)
        from (by
          unfold
            nb078AlphaDummy351;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0348)
                  0)))) (show (nb078AlphaDummy350 g) ≠ (nb078AlphaDummy352 g) from (by
          unfold
            nb078AlphaDummy352;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0349
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy347), (nb078AlphaDummy350 g)), ((nb078AlphaDummy346),
        (nb078AlphaDummy349 g)), ((nb078AlphaDummy345), (nb078AlphaDummy348 g)),
        ((nb078AlphaDummy343), (nb078AlphaDummy344 g)), ((nb078AlphaDummy339),
        (nb078AlphaDummy341 g)), ((nb078AlphaDummy340), (nb078AlphaDummy342 g)),
        ((nb078AlphaDummy332), (nb078AlphaDummy334 g)), ((nb078AlphaDummy331),
        (nb078AlphaDummy333 g)), ((nb078AlphaDummy337), (nb078AlphaDummy338 g)),
        ((nb078AlphaDummy335), (nb078AlphaDummy336 g)), ((nb078AlphaDummy289),
        (nb078AlphaDummy292 g)), ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
        ((nb078AlphaDummy287), (nb078AlphaDummy290 g)), ((nb078AlphaDummy293),
        (nb078AlphaDummy294 g)), ((nb078AlphaDummy285), (nb078AlphaDummy286 g)),
        ((nb078AlphaDummy283), (nb078AlphaDummy284 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy339))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy341 g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb078AlphaDummy339))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy341 g))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy346) ≠
        (nb078AlphaDummy357) from (by
          unfold
            nb078AlphaDummy357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0354)
                  0)))) (show (nb078AlphaDummy349 g) ≠ (nb078AlphaDummy358 g) from (by
          unfold
            nb078AlphaDummy358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0355
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy346) ≠ (nb078AlphaDummy355)
        from (by
          unfold
            nb078AlphaDummy355;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0352)
                  0)))) (show (nb078AlphaDummy349 g) ≠ (nb078AlphaDummy356 g) from (by
          unfold
            nb078AlphaDummy356;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0353
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy339))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy341 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy346) ≠ (nb078AlphaDummy357)
        from (by
          unfold
            nb078AlphaDummy357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0354)
                  0)))) (show (nb078AlphaDummy349 g) ≠ (nb078AlphaDummy358 g) from (by
          unfold
            nb078AlphaDummy358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0355
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy346) ≠ (nb078AlphaDummy355)
        from (by
          unfold
            nb078AlphaDummy355;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0352)
                  0)))) (show (nb078AlphaDummy349 g) ≠ (nb078AlphaDummy356 g) from (by
          unfold
            nb078AlphaDummy356;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0353
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy339))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy341 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy347) ≠ (nb078AlphaDummy359) from (by
          unfold
            nb078AlphaDummy359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0358)
                  0)))) (show (nb078AlphaDummy350 g) ≠ (nb078AlphaDummy360 g) from (by
          unfold
            nb078AlphaDummy360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0359
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy347) ≠ (nb078AlphaDummy355)
        from (by
          unfold
            nb078AlphaDummy355;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0356)
                  0)))) (show (nb078AlphaDummy350 g) ≠ (nb078AlphaDummy356 g) from (by
          unfold
            nb078AlphaDummy356;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0357
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy347) ≠
        (nb078AlphaDummy359) from (by
          unfold
            nb078AlphaDummy359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0358)
                  0)))) (show (nb078AlphaDummy350 g) ≠ (nb078AlphaDummy360 g) from (by
          unfold
            nb078AlphaDummy360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0359
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy347) ≠ (nb078AlphaDummy355)
        from (by
          unfold
            nb078AlphaDummy355;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0356)
                  0)))) (show (nb078AlphaDummy350 g) ≠ (nb078AlphaDummy356 g) from (by
          unfold
            nb078AlphaDummy356;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0357
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy339) ≠ (nb078AlphaDummy343) from (by
                                        unfold nb078AlphaDummy343;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0340)
                                                0)))) (show (nb078AlphaDummy341 g) ≠
                                        (nb078AlphaDummy344 g) from (by
                                        unfold nb078AlphaDummy344;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0341 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy343), (nb078AlphaDummy344 g)),
                                    ((nb078AlphaDummy339), (nb078AlphaDummy341 g)),
                                    ((nb078AlphaDummy340), (nb078AlphaDummy342 g)),
                                    ((nb078AlphaDummy332), (nb078AlphaDummy334 g)),
                                    ((nb078AlphaDummy331), (nb078AlphaDummy333 g)),
                                    ((nb078AlphaDummy337), (nb078AlphaDummy338 g)),
                                    ((nb078AlphaDummy335), (nb078AlphaDummy336 g)),
                                    ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
                                    ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
                                    ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
                                    ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
                                    ((nb078AlphaDummy285), (nb078AlphaDummy286 g)),
                                    ((nb078AlphaDummy283), (nb078AlphaDummy284 g)),
                                    ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy339) ≠ (nb078AlphaDummy343) from
                                    (by
                                      unfold nb078AlphaDummy343;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0340)
                                              0)))) (show
                                    (nb078AlphaDummy341 g) ≠ (nb078AlphaDummy344 g) from
                                    (by
                                      unfold nb078AlphaDummy344;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0341 g)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy339) ≠ (nb078AlphaDummy343) from (by
                                        unfold nb078AlphaDummy343;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0340)
                                                0)))) (show (nb078AlphaDummy341 g) ≠
                                        (nb078AlphaDummy344 g) from (by
                                        unfold nb078AlphaDummy344;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0341 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy343), (nb078AlphaDummy344 g)),
                                    ((nb078AlphaDummy339), (nb078AlphaDummy341 g)),
                                    ((nb078AlphaDummy340), (nb078AlphaDummy342 g)),
                                    ((nb078AlphaDummy332), (nb078AlphaDummy334 g)),
                                    ((nb078AlphaDummy331), (nb078AlphaDummy333 g)),
                                    ((nb078AlphaDummy337), (nb078AlphaDummy338 g)),
                                    ((nb078AlphaDummy335), (nb078AlphaDummy336 g)),
                                    ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
                                    ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
                                    ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
                                    ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
                                    ((nb078AlphaDummy285), (nb078AlphaDummy286 g)),
                                    ((nb078AlphaDummy283), (nb078AlphaDummy284 g)),
                                    ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078AlphaDummy287) ≠ (nb078AlphaDummy332) from
                      (by
                        unfold nb078AlphaDummy332;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0332) 1))))
                    (show (nb078AlphaDummy290 g) ≠ (nb078AlphaDummy334 g) from (by
                        unfold nb078AlphaDummy334;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0334 g) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy287) ≠ (nb078AlphaDummy331) from (by
                          unfold nb078AlphaDummy331;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0332) 0))))
                      (show (nb078AlphaDummy290 g) ≠ (nb078AlphaDummy333 g) from (by
                          unfold nb078AlphaDummy333;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0334 g) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy287) ≠ (nb078AlphaDummy337) from (by
                            unfold nb078AlphaDummy337;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0336) 0))))
                        (show (nb078AlphaDummy290 g) ≠ (nb078AlphaDummy338 g) from (by
                            unfold nb078AlphaDummy338;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0337 g) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy287) ≠ (nb078AlphaDummy335) from (by
                              unfold nb078AlphaDummy335;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0333) 0))))
                          (show (nb078AlphaDummy290 g) ≠ (nb078AlphaDummy336 g) from (by
                              unfold nb078AlphaDummy336;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0335 g) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb078AlphaDummy001))).fv ∪
                                ((synCcnv (Class.cv (nb078AlphaDummy001)))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv g)).fv ∪ ((synCcnv (Class.cv g))).fv) (by decide))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb078AlphaDummy001))).fv ∪
                                  ((synCcnv (Class.cv (nb078AlphaDummy001)))).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv g)).fv ∪ ((synCcnv (Class.cv g))).fv) (by decide))
                              (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078AlphaDummy287))).fv ∪
                        ((Class.cv (nb078AlphaDummy289))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy290 g))).fv ∪
                        ((Class.cv (nb078AlphaDummy292 g))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy332) ≠ (nb078AlphaDummy339) from (by
                                unfold nb078AlphaDummy339;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0338) 0))))
                            (show (nb078AlphaDummy334 g) ≠ (nb078AlphaDummy341 g) from (by
                                unfold nb078AlphaDummy341;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0339 g) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy332) ≠ (nb078AlphaDummy340) from (by
                                  unfold nb078AlphaDummy340;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0338) 1))))
                              (show (nb078AlphaDummy334 g) ≠ (nb078AlphaDummy342 g) from
                                (by
                                  unfold nb078AlphaDummy342;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0339 g) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy332))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy334 g))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy339) ≠ (nb078AlphaDummy346) from (by
          unfold nb078AlphaDummy346;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0342) 1)))) (show (nb078AlphaDummy341 g) ≠
        (nb078AlphaDummy349 g) from (by
          unfold nb078AlphaDummy349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0343 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy339) ≠ (nb078AlphaDummy345) from (by
          unfold nb078AlphaDummy345;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0342) 0)))) (show (nb078AlphaDummy341 g) ≠
        (nb078AlphaDummy348 g) from (by
          unfold nb078AlphaDummy348;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0343 g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy339) ≠ (nb078AlphaDummy343)
        from (by
          unfold nb078AlphaDummy343;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0340)
                  0)))) (show (nb078AlphaDummy341 g) ≠ (nb078AlphaDummy344 g) from (by
          unfold nb078AlphaDummy344;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0341 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy347), (nb078AlphaDummy350 g)), ((nb078AlphaDummy346),
        (nb078AlphaDummy349 g)), ((nb078AlphaDummy345), (nb078AlphaDummy348 g)),
        ((nb078AlphaDummy343), (nb078AlphaDummy344 g)), ((nb078AlphaDummy339),
        (nb078AlphaDummy341 g)), ((nb078AlphaDummy340), (nb078AlphaDummy342 g)),
        ((nb078AlphaDummy332), (nb078AlphaDummy334 g)), ((nb078AlphaDummy331),
        (nb078AlphaDummy333 g)), ((nb078AlphaDummy337), (nb078AlphaDummy338 g)),
        ((nb078AlphaDummy335), (nb078AlphaDummy336 g)), ((nb078AlphaDummy289),
        (nb078AlphaDummy292 g)), ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
        ((nb078AlphaDummy287), (nb078AlphaDummy290 g)), ((nb078AlphaDummy293),
        (nb078AlphaDummy294 g)), ((nb078AlphaDummy285), (nb078AlphaDummy286 g)),
        ((nb078AlphaDummy283), (nb078AlphaDummy284 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy346) ≠ (nb078AlphaDummy353) from (by
          unfold
            nb078AlphaDummy353;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0346)
                  0)))) (show (nb078AlphaDummy349 g) ≠ (nb078AlphaDummy354 g) from (by
          unfold
            nb078AlphaDummy354;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0347
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy346) ≠ (nb078AlphaDummy351)
        from (by
          unfold
            nb078AlphaDummy351;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0344)
                  0)))) (show (nb078AlphaDummy349 g) ≠ (nb078AlphaDummy352 g) from (by
          unfold
            nb078AlphaDummy352;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0345
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy339))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy341 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy347) ≠ (nb078AlphaDummy353)
        from (by
          unfold
            nb078AlphaDummy353;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0350)
                  0)))) (show (nb078AlphaDummy350 g) ≠ (nb078AlphaDummy354 g) from (by
          unfold
            nb078AlphaDummy354;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0351
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy347) ≠ (nb078AlphaDummy351)
        from (by
          unfold
            nb078AlphaDummy351;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0348)
                  0)))) (show (nb078AlphaDummy350 g) ≠ (nb078AlphaDummy352 g) from (by
          unfold
            nb078AlphaDummy352;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0349
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy346) ≠ (nb078AlphaDummy353) from (by
          unfold
            nb078AlphaDummy353;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0346)
                  0)))) (show (nb078AlphaDummy349 g) ≠ (nb078AlphaDummy354 g) from (by
          unfold
            nb078AlphaDummy354;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0347
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy346) ≠ (nb078AlphaDummy351)
        from (by
          unfold
            nb078AlphaDummy351;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0344)
                  0)))) (show (nb078AlphaDummy349 g) ≠ (nb078AlphaDummy352 g) from (by
          unfold
            nb078AlphaDummy352;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0345
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy339))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy341 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy347) ≠ (nb078AlphaDummy353)
        from (by
          unfold
            nb078AlphaDummy353;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0350)
                  0)))) (show (nb078AlphaDummy350 g) ≠ (nb078AlphaDummy354 g) from (by
          unfold
            nb078AlphaDummy354;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0351
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy347) ≠ (nb078AlphaDummy351)
        from (by
          unfold
            nb078AlphaDummy351;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0348)
                  0)))) (show (nb078AlphaDummy350 g) ≠ (nb078AlphaDummy352 g) from (by
          unfold
            nb078AlphaDummy352;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0349
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy347), (nb078AlphaDummy350 g)), ((nb078AlphaDummy346),
        (nb078AlphaDummy349 g)), ((nb078AlphaDummy345), (nb078AlphaDummy348 g)),
        ((nb078AlphaDummy343), (nb078AlphaDummy344 g)), ((nb078AlphaDummy339),
        (nb078AlphaDummy341 g)), ((nb078AlphaDummy340), (nb078AlphaDummy342 g)),
        ((nb078AlphaDummy332), (nb078AlphaDummy334 g)), ((nb078AlphaDummy331),
        (nb078AlphaDummy333 g)), ((nb078AlphaDummy337), (nb078AlphaDummy338 g)),
        ((nb078AlphaDummy335), (nb078AlphaDummy336 g)), ((nb078AlphaDummy289),
        (nb078AlphaDummy292 g)), ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
        ((nb078AlphaDummy287), (nb078AlphaDummy290 g)), ((nb078AlphaDummy293),
        (nb078AlphaDummy294 g)), ((nb078AlphaDummy285), (nb078AlphaDummy286 g)),
        ((nb078AlphaDummy283), (nb078AlphaDummy284 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy339))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy341
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy339))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy341 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy346) ≠
        (nb078AlphaDummy357) from (by
          unfold
            nb078AlphaDummy357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0354)
                  0)))) (show (nb078AlphaDummy349 g) ≠ (nb078AlphaDummy358 g) from (by
          unfold
            nb078AlphaDummy358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0355
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy346) ≠ (nb078AlphaDummy355)
        from (by
          unfold
            nb078AlphaDummy355;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0352)
                  0)))) (show (nb078AlphaDummy349 g) ≠ (nb078AlphaDummy356 g) from (by
          unfold
            nb078AlphaDummy356;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0353
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy339))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy341 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy346) ≠ (nb078AlphaDummy357)
        from (by
          unfold
            nb078AlphaDummy357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0354)
                  0)))) (show (nb078AlphaDummy349 g) ≠ (nb078AlphaDummy358 g) from (by
          unfold
            nb078AlphaDummy358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0355
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy346) ≠ (nb078AlphaDummy355)
        from (by
          unfold
            nb078AlphaDummy355;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0352)
                  0)))) (show (nb078AlphaDummy349 g) ≠ (nb078AlphaDummy356 g) from (by
          unfold
            nb078AlphaDummy356;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0353
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy339))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy341 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy347) ≠ (nb078AlphaDummy359) from (by
          unfold
            nb078AlphaDummy359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0358)
                  0)))) (show (nb078AlphaDummy350 g) ≠ (nb078AlphaDummy360 g) from (by
          unfold
            nb078AlphaDummy360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0359
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy347) ≠ (nb078AlphaDummy355)
        from (by
          unfold
            nb078AlphaDummy355;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0356)
                  0)))) (show (nb078AlphaDummy350 g) ≠ (nb078AlphaDummy356 g) from (by
          unfold
            nb078AlphaDummy356;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0357
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy347) ≠
        (nb078AlphaDummy359) from (by
          unfold
            nb078AlphaDummy359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0358)
                  0)))) (show (nb078AlphaDummy350 g) ≠ (nb078AlphaDummy360 g) from (by
          unfold
            nb078AlphaDummy360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0359
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy347) ≠ (nb078AlphaDummy355)
        from (by
          unfold
            nb078AlphaDummy355;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0356)
                  0)))) (show (nb078AlphaDummy350 g) ≠ (nb078AlphaDummy356 g) from (by
          unfold
            nb078AlphaDummy356;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0357
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy339) ≠ (nb078AlphaDummy343) from
                                        (by
                                          unfold nb078AlphaDummy343;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0340)
                                                  0)))) (show (nb078AlphaDummy341 g) ≠
        (nb078AlphaDummy344 g) from (by
                                          unfold nb078AlphaDummy344;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0341 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy343), (nb078AlphaDummy344 g)),
                                      ((nb078AlphaDummy339), (nb078AlphaDummy341 g)),
                                      ((nb078AlphaDummy340), (nb078AlphaDummy342 g)),
                                      ((nb078AlphaDummy332), (nb078AlphaDummy334 g)),
                                      ((nb078AlphaDummy331), (nb078AlphaDummy333 g)),
                                      ((nb078AlphaDummy337), (nb078AlphaDummy338 g)),
                                      ((nb078AlphaDummy335), (nb078AlphaDummy336 g)),
                                      ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
                                      ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
                                      ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
                                      ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
                                      ((nb078AlphaDummy285), (nb078AlphaDummy286 g)),
                                      ((nb078AlphaDummy283), (nb078AlphaDummy284 g)),
                                      ((nb078AlphaDummy001), g),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy339) ≠ (nb078AlphaDummy343) from (by
                                        unfold nb078AlphaDummy343;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0340)
                                                0)))) (show (nb078AlphaDummy341 g) ≠
                                        (nb078AlphaDummy344 g) from (by
                                        unfold nb078AlphaDummy344;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0341 g)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy339) ≠ (nb078AlphaDummy343) from
                                        (by
                                          unfold nb078AlphaDummy343;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0340)
                                                  0)))) (show (nb078AlphaDummy341 g) ≠
        (nb078AlphaDummy344 g) from (by
                                          unfold nb078AlphaDummy344;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0341 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy343), (nb078AlphaDummy344 g)),
                                      ((nb078AlphaDummy339), (nb078AlphaDummy341 g)),
                                      ((nb078AlphaDummy340), (nb078AlphaDummy342 g)),
                                      ((nb078AlphaDummy332), (nb078AlphaDummy334 g)),
                                      ((nb078AlphaDummy331), (nb078AlphaDummy333 g)),
                                      ((nb078AlphaDummy337), (nb078AlphaDummy338 g)),
                                      ((nb078AlphaDummy335), (nb078AlphaDummy336 g)),
                                      ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
                                      ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
                                      ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
                                      ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
                                      ((nb078AlphaDummy285), (nb078AlphaDummy286 g)),
                                      ((nb078AlphaDummy283), (nb078AlphaDummy284 g)),
                                      ((nb078AlphaDummy001), g),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
