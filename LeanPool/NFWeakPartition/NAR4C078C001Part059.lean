/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C078C001Part057

/-! NF weak partition development: NAR4C078C001Part059. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0028`. -/
@[expose]
noncomputable def nb078SplitAlpha0028 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb078AlphaDummy248), (nb078AlphaDummy250 f)),
        ((nb078AlphaDummy247), (nb078AlphaDummy249 f)),
        ((nb078AlphaDummy277), (nb078AlphaDummy278 f)),
        ((nb078AlphaDummy251), (nb078AlphaDummy252 f)),
        ((nb078AlphaDummy244), (nb078AlphaDummy246 f)),
        ((nb078AlphaDummy243), (nb078AlphaDummy245 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy248))
          (Class.cv (nb078AlphaDummy243))) (Wff.neg
          (Wff.classEq (Class.cv (nb078AlphaDummy247))
            (synCun (synCphi (Class.cv (nb078AlphaDummy248))) (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy250 f))
          (Class.cv (nb078AlphaDummy245 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb078AlphaDummy249 f))
            (synCun (synCphi (Class.cv (nb078AlphaDummy250 f))) (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy243) ≠ (nb078AlphaDummy248) from (by
              unfold nb078AlphaDummy248;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0278) 1))))
          (show (nb078AlphaDummy245 f) ≠ (nb078AlphaDummy250 f) from (by
              unfold nb078AlphaDummy250;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0280 f) 1))))
          (TAlphaVar.there (show (nb078AlphaDummy243) ≠ (nb078AlphaDummy247) from (by
                unfold nb078AlphaDummy247;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0278) 0))))
            (show (nb078AlphaDummy245 f) ≠ (nb078AlphaDummy249 f) from (by
                unfold nb078AlphaDummy249;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0280 f) 0))))
            (TAlphaVar.there (show (nb078AlphaDummy243) ≠ (nb078AlphaDummy277) from (by
                  unfold nb078AlphaDummy277;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0282) 0))))
              (show (nb078AlphaDummy245 f) ≠ (nb078AlphaDummy278 f) from (by
                  unfold nb078AlphaDummy278;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0283 f) 0))))
              (TAlphaVar.there (show (nb078AlphaDummy243) ≠ (nb078AlphaDummy251) from (by
                    unfold nb078AlphaDummy251;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0279) 0))))
                (show (nb078AlphaDummy245 f) ≠ (nb078AlphaDummy252 f) from (by
                    unfold nb078AlphaDummy252;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0281 f) 0))))
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb078AlphaDummy000))).fv ∪ ((synCvv)).fv) (by decide))
                  (freshVar_injective (((Class.cv f)).fv ∪ ((synCvv)).fv) (by decide))
                  (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb078AlphaDummy244))).fv ∪
                ((Class.cv (nb078AlphaDummy243))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb078AlphaDummy246 f))).fv ∪
                ((Class.cv (nb078AlphaDummy245 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy248) ≠ (nb078AlphaDummy255) from (by
                                        unfold nb078AlphaDummy255;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0256)
                                                0)))) (show (nb078AlphaDummy250 f) ≠
                                        (nb078AlphaDummy257 f) from (by
                                        unfold nb078AlphaDummy257;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0257 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy248) ≠ (nb078AlphaDummy256) from
                                        (by
                                          unfold nb078AlphaDummy256;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0256)
                                                  1)))) (show (nb078AlphaDummy250 f) ≠
        (nb078AlphaDummy258 f) from (by
                                          unfold nb078AlphaDummy258;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0257 f) 1))))
                                      (TAlphaVar.there (show (nb078AlphaDummy248) ≠
        (nb078AlphaDummy281) from (by
          unfold nb078AlphaDummy281;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0286) 0)))) (show (nb078AlphaDummy250 f) ≠
        (nb078AlphaDummy282 f) from (by
          unfold nb078AlphaDummy282;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0287 f) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy248) ≠ (nb078AlphaDummy279) from (by
          unfold nb078AlphaDummy279;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0284) 0)))) (show (nb078AlphaDummy250 f) ≠
        (nb078AlphaDummy280 f) from (by
          unfold nb078AlphaDummy280;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0285 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb078AlphaDummy248))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb078AlphaDummy250 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy255) ≠ (nb078AlphaDummy262) from (by
          unfold nb078AlphaDummy262;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0260)
                  1)))) (show (nb078AlphaDummy257 f) ≠ (nb078AlphaDummy265 f) from (by
          unfold nb078AlphaDummy265;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0261
                    f)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy255) ≠ (nb078AlphaDummy261)
        from (by
          unfold nb078AlphaDummy261;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0260)
                  0)))) (show (nb078AlphaDummy257 f) ≠ (nb078AlphaDummy264 f) from (by
          unfold nb078AlphaDummy264;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0261
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy255) ≠ (nb078AlphaDummy259)
        from (by
          unfold
            nb078AlphaDummy259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0258)
                  0)))) (show (nb078AlphaDummy257 f) ≠ (nb078AlphaDummy260 f) from (by
          unfold
            nb078AlphaDummy260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0259
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy263), (nb078AlphaDummy266 f)), ((nb078AlphaDummy262),
        (nb078AlphaDummy265 f)), ((nb078AlphaDummy261), (nb078AlphaDummy264 f)),
        ((nb078AlphaDummy259), (nb078AlphaDummy260 f)), ((nb078AlphaDummy255),
        (nb078AlphaDummy257 f)), ((nb078AlphaDummy256), (nb078AlphaDummy258 f)),
        ((nb078AlphaDummy281), (nb078AlphaDummy282 f)), ((nb078AlphaDummy279),
        (nb078AlphaDummy280 f)), ((nb078AlphaDummy248), (nb078AlphaDummy250 f)),
        ((nb078AlphaDummy247), (nb078AlphaDummy249 f)), ((nb078AlphaDummy277),
        (nb078AlphaDummy278 f)), ((nb078AlphaDummy251), (nb078AlphaDummy252 f)),
        ((nb078AlphaDummy244), (nb078AlphaDummy246 f)), ((nb078AlphaDummy243),
        (nb078AlphaDummy245 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy262) ≠ (nb078AlphaDummy269) from (by
          unfold
            nb078AlphaDummy269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0264)
                  0)))) (show (nb078AlphaDummy265 f) ≠ (nb078AlphaDummy270 f) from (by
          unfold
            nb078AlphaDummy270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0265
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy262) ≠ (nb078AlphaDummy267)
        from (by
          unfold
            nb078AlphaDummy267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0262)
                  0)))) (show (nb078AlphaDummy265 f) ≠ (nb078AlphaDummy268 f) from (by
          unfold
            nb078AlphaDummy268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0263
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy255))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy257 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy263) ≠
        (nb078AlphaDummy269) from (by
          unfold
            nb078AlphaDummy269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0268)
                  0)))) (show (nb078AlphaDummy266 f) ≠ (nb078AlphaDummy270 f) from (by
          unfold
            nb078AlphaDummy270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0269
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy263) ≠ (nb078AlphaDummy267)
        from (by
          unfold
            nb078AlphaDummy267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0266)
                  0)))) (show (nb078AlphaDummy266 f) ≠ (nb078AlphaDummy268 f) from (by
          unfold
            nb078AlphaDummy268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0267
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy262) ≠ (nb078AlphaDummy269) from (by
          unfold
            nb078AlphaDummy269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0264)
                  0)))) (show (nb078AlphaDummy265 f) ≠ (nb078AlphaDummy270 f) from (by
          unfold
            nb078AlphaDummy270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0265
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy262) ≠ (nb078AlphaDummy267)
        from (by
          unfold
            nb078AlphaDummy267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0262)
                  0)))) (show (nb078AlphaDummy265 f) ≠ (nb078AlphaDummy268 f) from (by
          unfold
            nb078AlphaDummy268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0263
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy255))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy257 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy263) ≠
        (nb078AlphaDummy269) from (by
          unfold
            nb078AlphaDummy269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0268)
                  0)))) (show (nb078AlphaDummy266 f) ≠ (nb078AlphaDummy270 f) from (by
          unfold
            nb078AlphaDummy270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0269
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy263) ≠ (nb078AlphaDummy267)
        from (by
          unfold
            nb078AlphaDummy267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0266)
                  0)))) (show (nb078AlphaDummy266 f) ≠ (nb078AlphaDummy268 f) from (by
          unfold
            nb078AlphaDummy268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0267
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy263), (nb078AlphaDummy266 f)), ((nb078AlphaDummy262),
        (nb078AlphaDummy265 f)), ((nb078AlphaDummy261), (nb078AlphaDummy264 f)),
        ((nb078AlphaDummy259), (nb078AlphaDummy260 f)), ((nb078AlphaDummy255),
        (nb078AlphaDummy257 f)), ((nb078AlphaDummy256), (nb078AlphaDummy258 f)),
        ((nb078AlphaDummy281), (nb078AlphaDummy282 f)), ((nb078AlphaDummy279),
        (nb078AlphaDummy280 f)), ((nb078AlphaDummy248), (nb078AlphaDummy250 f)),
        ((nb078AlphaDummy247), (nb078AlphaDummy249 f)), ((nb078AlphaDummy277),
        (nb078AlphaDummy278 f)), ((nb078AlphaDummy251), (nb078AlphaDummy252 f)),
        ((nb078AlphaDummy244), (nb078AlphaDummy246 f)), ((nb078AlphaDummy243),
        (nb078AlphaDummy245 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy255))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy257 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy255))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy257
        f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy262) ≠ (nb078AlphaDummy273) from (by
          unfold
            nb078AlphaDummy273;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0272)
                  0)))) (show (nb078AlphaDummy265 f) ≠ (nb078AlphaDummy274 f) from (by
          unfold
            nb078AlphaDummy274;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0273
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy262) ≠ (nb078AlphaDummy271)
        from (by
          unfold
            nb078AlphaDummy271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0270)
                  0)))) (show (nb078AlphaDummy265 f) ≠ (nb078AlphaDummy272 f) from (by
          unfold
            nb078AlphaDummy272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0271
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy255))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy257 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy262) ≠
        (nb078AlphaDummy273) from (by
          unfold
            nb078AlphaDummy273;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0272)
                  0)))) (show (nb078AlphaDummy265 f) ≠ (nb078AlphaDummy274 f) from (by
          unfold
            nb078AlphaDummy274;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0273
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy262) ≠ (nb078AlphaDummy271)
        from (by
          unfold
            nb078AlphaDummy271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0270)
                  0)))) (show (nb078AlphaDummy265 f) ≠ (nb078AlphaDummy272 f) from (by
          unfold
            nb078AlphaDummy272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0271
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy255))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy257 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy263) ≠ (nb078AlphaDummy275) from (by
          unfold
            nb078AlphaDummy275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0276)
                  0)))) (show (nb078AlphaDummy266 f) ≠ (nb078AlphaDummy276 f) from (by
          unfold
            nb078AlphaDummy276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0277
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy263) ≠ (nb078AlphaDummy271)
        from (by
          unfold
            nb078AlphaDummy271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0274)
                  0)))) (show (nb078AlphaDummy266 f) ≠ (nb078AlphaDummy272 f) from (by
          unfold
            nb078AlphaDummy272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0275
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy263) ≠
        (nb078AlphaDummy275) from (by
          unfold
            nb078AlphaDummy275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0276)
                  0)))) (show (nb078AlphaDummy266 f) ≠ (nb078AlphaDummy276 f) from (by
          unfold
            nb078AlphaDummy276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0277
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy263) ≠ (nb078AlphaDummy271)
        from (by
          unfold
            nb078AlphaDummy271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0274)
                  0)))) (show (nb078AlphaDummy266 f) ≠ (nb078AlphaDummy272 f) from (by
          unfold
            nb078AlphaDummy272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0275
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy255) ≠ (nb078AlphaDummy259)
        from (by
          unfold nb078AlphaDummy259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0258) 0)))) (show (nb078AlphaDummy257 f) ≠
        (nb078AlphaDummy260 f) from (by
          unfold nb078AlphaDummy260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0259 f) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb078AlphaDummy259), (nb078AlphaDummy260 f)),
        ((nb078AlphaDummy255), (nb078AlphaDummy257 f)), ((nb078AlphaDummy256),
        (nb078AlphaDummy258 f)), ((nb078AlphaDummy281), (nb078AlphaDummy282 f)),
        ((nb078AlphaDummy279), (nb078AlphaDummy280 f)), ((nb078AlphaDummy248),
        (nb078AlphaDummy250 f)), ((nb078AlphaDummy247), (nb078AlphaDummy249 f)),
        ((nb078AlphaDummy277), (nb078AlphaDummy278 f)), ((nb078AlphaDummy251),
        (nb078AlphaDummy252 f)), ((nb078AlphaDummy244), (nb078AlphaDummy246 f)),
        ((nb078AlphaDummy243), (nb078AlphaDummy245 f)), ((nb078AlphaDummy000), f),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy255) ≠ (nb078AlphaDummy259) from (by
          unfold nb078AlphaDummy259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0258) 0)))) (show (nb078AlphaDummy257 f) ≠
        (nb078AlphaDummy260 f) from (by
          unfold nb078AlphaDummy260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0259 f) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb078AlphaDummy255) ≠ (nb078AlphaDummy259) from (by
          unfold nb078AlphaDummy259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0258) 0)))) (show (nb078AlphaDummy257 f) ≠
        (nb078AlphaDummy260 f) from (by
          unfold nb078AlphaDummy260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0259 f) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb078AlphaDummy259), (nb078AlphaDummy260 f)),
        ((nb078AlphaDummy255), (nb078AlphaDummy257 f)), ((nb078AlphaDummy256),
        (nb078AlphaDummy258 f)), ((nb078AlphaDummy281), (nb078AlphaDummy282 f)),
        ((nb078AlphaDummy279), (nb078AlphaDummy280 f)), ((nb078AlphaDummy248),
        (nb078AlphaDummy250 f)), ((nb078AlphaDummy247), (nb078AlphaDummy249 f)),
        ((nb078AlphaDummy277), (nb078AlphaDummy278 f)), ((nb078AlphaDummy251),
        (nb078AlphaDummy252 f)), ((nb078AlphaDummy244), (nb078AlphaDummy246 f)),
        ((nb078AlphaDummy243), (nb078AlphaDummy245 f)), ((nb078AlphaDummy000), f),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)] (synCnnc)
        (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy248) ≠ (nb078AlphaDummy255) from (by
                                        unfold nb078AlphaDummy255;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0256)
                                                0)))) (show (nb078AlphaDummy250 f) ≠
                                        (nb078AlphaDummy257 f) from (by
                                        unfold nb078AlphaDummy257;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0257 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy248) ≠ (nb078AlphaDummy256) from
                                        (by
                                          unfold nb078AlphaDummy256;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0256)
                                                  1)))) (show (nb078AlphaDummy250 f) ≠
        (nb078AlphaDummy258 f) from (by
                                          unfold nb078AlphaDummy258;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0257 f) 1))))
                                      (TAlphaVar.there (show (nb078AlphaDummy248) ≠
        (nb078AlphaDummy281) from (by
          unfold nb078AlphaDummy281;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0286) 0)))) (show (nb078AlphaDummy250 f) ≠
        (nb078AlphaDummy282 f) from (by
          unfold nb078AlphaDummy282;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0287 f) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy248) ≠ (nb078AlphaDummy279) from (by
          unfold nb078AlphaDummy279;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0284) 0)))) (show (nb078AlphaDummy250 f) ≠
        (nb078AlphaDummy280 f) from (by
          unfold nb078AlphaDummy280;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0285 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb078AlphaDummy248))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb078AlphaDummy250 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy255) ≠ (nb078AlphaDummy262) from (by
          unfold nb078AlphaDummy262;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0260)
                  1)))) (show (nb078AlphaDummy257 f) ≠ (nb078AlphaDummy265 f) from (by
          unfold nb078AlphaDummy265;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0261
                    f)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy255) ≠ (nb078AlphaDummy261)
        from (by
          unfold nb078AlphaDummy261;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0260)
                  0)))) (show (nb078AlphaDummy257 f) ≠ (nb078AlphaDummy264 f) from (by
          unfold nb078AlphaDummy264;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0261
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy255) ≠ (nb078AlphaDummy259)
        from (by
          unfold
            nb078AlphaDummy259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0258)
                  0)))) (show (nb078AlphaDummy257 f) ≠ (nb078AlphaDummy260 f) from (by
          unfold
            nb078AlphaDummy260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0259
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy263), (nb078AlphaDummy266 f)), ((nb078AlphaDummy262),
        (nb078AlphaDummy265 f)), ((nb078AlphaDummy261), (nb078AlphaDummy264 f)),
        ((nb078AlphaDummy259), (nb078AlphaDummy260 f)), ((nb078AlphaDummy255),
        (nb078AlphaDummy257 f)), ((nb078AlphaDummy256), (nb078AlphaDummy258 f)),
        ((nb078AlphaDummy281), (nb078AlphaDummy282 f)), ((nb078AlphaDummy279),
        (nb078AlphaDummy280 f)), ((nb078AlphaDummy248), (nb078AlphaDummy250 f)),
        ((nb078AlphaDummy247), (nb078AlphaDummy249 f)), ((nb078AlphaDummy277),
        (nb078AlphaDummy278 f)), ((nb078AlphaDummy251), (nb078AlphaDummy252 f)),
        ((nb078AlphaDummy244), (nb078AlphaDummy246 f)), ((nb078AlphaDummy243),
        (nb078AlphaDummy245 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy262) ≠ (nb078AlphaDummy269) from (by
          unfold
            nb078AlphaDummy269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0264)
                  0)))) (show (nb078AlphaDummy265 f) ≠ (nb078AlphaDummy270 f) from (by
          unfold
            nb078AlphaDummy270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0265
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy262) ≠ (nb078AlphaDummy267)
        from (by
          unfold
            nb078AlphaDummy267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0262)
                  0)))) (show (nb078AlphaDummy265 f) ≠ (nb078AlphaDummy268 f) from (by
          unfold
            nb078AlphaDummy268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0263
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy255))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy257 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy263) ≠
        (nb078AlphaDummy269) from (by
          unfold
            nb078AlphaDummy269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0268)
                  0)))) (show (nb078AlphaDummy266 f) ≠ (nb078AlphaDummy270 f) from (by
          unfold
            nb078AlphaDummy270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0269
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy263) ≠ (nb078AlphaDummy267)
        from (by
          unfold
            nb078AlphaDummy267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0266)
                  0)))) (show (nb078AlphaDummy266 f) ≠ (nb078AlphaDummy268 f) from (by
          unfold
            nb078AlphaDummy268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0267
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy262) ≠ (nb078AlphaDummy269) from (by
          unfold
            nb078AlphaDummy269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0264)
                  0)))) (show (nb078AlphaDummy265 f) ≠ (nb078AlphaDummy270 f) from (by
          unfold
            nb078AlphaDummy270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0265
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy262) ≠ (nb078AlphaDummy267)
        from (by
          unfold
            nb078AlphaDummy267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0262)
                  0)))) (show (nb078AlphaDummy265 f) ≠ (nb078AlphaDummy268 f) from (by
          unfold
            nb078AlphaDummy268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0263
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy255))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy257 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy263) ≠
        (nb078AlphaDummy269) from (by
          unfold
            nb078AlphaDummy269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0268)
                  0)))) (show (nb078AlphaDummy266 f) ≠ (nb078AlphaDummy270 f) from (by
          unfold
            nb078AlphaDummy270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0269
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy263) ≠ (nb078AlphaDummy267)
        from (by
          unfold
            nb078AlphaDummy267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0266)
                  0)))) (show (nb078AlphaDummy266 f) ≠ (nb078AlphaDummy268 f) from (by
          unfold
            nb078AlphaDummy268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0267
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy263), (nb078AlphaDummy266 f)), ((nb078AlphaDummy262),
        (nb078AlphaDummy265 f)), ((nb078AlphaDummy261), (nb078AlphaDummy264 f)),
        ((nb078AlphaDummy259), (nb078AlphaDummy260 f)), ((nb078AlphaDummy255),
        (nb078AlphaDummy257 f)), ((nb078AlphaDummy256), (nb078AlphaDummy258 f)),
        ((nb078AlphaDummy281), (nb078AlphaDummy282 f)), ((nb078AlphaDummy279),
        (nb078AlphaDummy280 f)), ((nb078AlphaDummy248), (nb078AlphaDummy250 f)),
        ((nb078AlphaDummy247), (nb078AlphaDummy249 f)), ((nb078AlphaDummy277),
        (nb078AlphaDummy278 f)), ((nb078AlphaDummy251), (nb078AlphaDummy252 f)),
        ((nb078AlphaDummy244), (nb078AlphaDummy246 f)), ((nb078AlphaDummy243),
        (nb078AlphaDummy245 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy255))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy257 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy255))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy257
        f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy262) ≠ (nb078AlphaDummy273) from (by
          unfold
            nb078AlphaDummy273;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0272)
                  0)))) (show (nb078AlphaDummy265 f) ≠ (nb078AlphaDummy274 f) from (by
          unfold
            nb078AlphaDummy274;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0273
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy262) ≠ (nb078AlphaDummy271)
        from (by
          unfold
            nb078AlphaDummy271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0270)
                  0)))) (show (nb078AlphaDummy265 f) ≠ (nb078AlphaDummy272 f) from (by
          unfold
            nb078AlphaDummy272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0271
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy255))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy257 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy262) ≠
        (nb078AlphaDummy273) from (by
          unfold
            nb078AlphaDummy273;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0272)
                  0)))) (show (nb078AlphaDummy265 f) ≠ (nb078AlphaDummy274 f) from (by
          unfold
            nb078AlphaDummy274;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0273
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy262) ≠ (nb078AlphaDummy271)
        from (by
          unfold
            nb078AlphaDummy271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0270)
                  0)))) (show (nb078AlphaDummy265 f) ≠ (nb078AlphaDummy272 f) from (by
          unfold
            nb078AlphaDummy272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0271
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy255))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy257 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy263) ≠ (nb078AlphaDummy275) from (by
          unfold
            nb078AlphaDummy275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0276)
                  0)))) (show (nb078AlphaDummy266 f) ≠ (nb078AlphaDummy276 f) from (by
          unfold
            nb078AlphaDummy276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0277
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy263) ≠ (nb078AlphaDummy271)
        from (by
          unfold
            nb078AlphaDummy271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0274)
                  0)))) (show (nb078AlphaDummy266 f) ≠ (nb078AlphaDummy272 f) from (by
          unfold
            nb078AlphaDummy272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0275
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy263) ≠
        (nb078AlphaDummy275) from (by
          unfold
            nb078AlphaDummy275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0276)
                  0)))) (show (nb078AlphaDummy266 f) ≠ (nb078AlphaDummy276 f) from (by
          unfold
            nb078AlphaDummy276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0277
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy263) ≠ (nb078AlphaDummy271)
        from (by
          unfold
            nb078AlphaDummy271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0274)
                  0)))) (show (nb078AlphaDummy266 f) ≠ (nb078AlphaDummy272 f) from (by
          unfold
            nb078AlphaDummy272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0275
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy255) ≠ (nb078AlphaDummy259)
        from (by
          unfold nb078AlphaDummy259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0258) 0)))) (show (nb078AlphaDummy257 f) ≠
        (nb078AlphaDummy260 f) from (by
          unfold nb078AlphaDummy260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0259 f) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb078AlphaDummy259), (nb078AlphaDummy260 f)),
        ((nb078AlphaDummy255), (nb078AlphaDummy257 f)), ((nb078AlphaDummy256),
        (nb078AlphaDummy258 f)), ((nb078AlphaDummy281), (nb078AlphaDummy282 f)),
        ((nb078AlphaDummy279), (nb078AlphaDummy280 f)), ((nb078AlphaDummy248),
        (nb078AlphaDummy250 f)), ((nb078AlphaDummy247), (nb078AlphaDummy249 f)),
        ((nb078AlphaDummy277), (nb078AlphaDummy278 f)), ((nb078AlphaDummy251),
        (nb078AlphaDummy252 f)), ((nb078AlphaDummy244), (nb078AlphaDummy246 f)),
        ((nb078AlphaDummy243), (nb078AlphaDummy245 f)), ((nb078AlphaDummy000), f),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy255) ≠ (nb078AlphaDummy259) from (by
          unfold nb078AlphaDummy259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0258) 0)))) (show (nb078AlphaDummy257 f) ≠
        (nb078AlphaDummy260 f) from (by
          unfold nb078AlphaDummy260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0259 f) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb078AlphaDummy255) ≠ (nb078AlphaDummy259) from (by
          unfold nb078AlphaDummy259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0258) 0)))) (show (nb078AlphaDummy257 f) ≠
        (nb078AlphaDummy260 f) from (by
          unfold nb078AlphaDummy260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0259 f) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb078AlphaDummy259), (nb078AlphaDummy260 f)),
        ((nb078AlphaDummy255), (nb078AlphaDummy257 f)), ((nb078AlphaDummy256),
        (nb078AlphaDummy258 f)), ((nb078AlphaDummy281), (nb078AlphaDummy282 f)),
        ((nb078AlphaDummy279), (nb078AlphaDummy280 f)), ((nb078AlphaDummy248),
        (nb078AlphaDummy250 f)), ((nb078AlphaDummy247), (nb078AlphaDummy249 f)),
        ((nb078AlphaDummy277), (nb078AlphaDummy278 f)), ((nb078AlphaDummy251),
        (nb078AlphaDummy252 f)), ((nb078AlphaDummy244), (nb078AlphaDummy246 f)),
        ((nb078AlphaDummy243), (nb078AlphaDummy245 f)), ((nb078AlphaDummy000), f),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)] (synCnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb078AlphaDummy279), (nb078AlphaDummy280 f)),
                    ((nb078AlphaDummy248), (nb078AlphaDummy250 f)),
                    ((nb078AlphaDummy247), (nb078AlphaDummy249 f)),
                    ((nb078AlphaDummy277), (nb078AlphaDummy278 f)),
                    ((nb078AlphaDummy251), (nb078AlphaDummy252 f)),
                    ((nb078AlphaDummy244), (nb078AlphaDummy246 f)),
                    ((nb078AlphaDummy243), (nb078AlphaDummy245 f)),
                    ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
                    ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0029`. -/
@[expose]
noncomputable def nb078SplitAlpha0029 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb078AlphaDummy251), (nb078AlphaDummy252 f)),
        ((nb078AlphaDummy244), (nb078AlphaDummy246 f)),
        ((nb078AlphaDummy243), (nb078AlphaDummy245 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy251)) (synCcompl
            (Class.cab (nb078AlphaDummy247)
              (synWrex (nb078AlphaDummy248) (Class.cv (nb078AlphaDummy244))
                (Wff.classEq (Class.cv (nb078AlphaDummy247))
                  (synCphi (Class.cv (nb078AlphaDummy248)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy251)) (synCcompl
              (Class.cab (nb078AlphaDummy247)
                (synWrex (nb078AlphaDummy248) (Class.cv (nb078AlphaDummy243))
                  (Wff.classEq (Class.cv (nb078AlphaDummy247))
                    (synCun (synCphi (Class.cv (nb078AlphaDummy248)))
                      (synCsn (synC0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy252 f)) (synCcompl
            (Class.cab (nb078AlphaDummy249 f)
              (synWrex (nb078AlphaDummy250 f) (Class.cv (nb078AlphaDummy246 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy249 f))
                  (synCphi (Class.cv (nb078AlphaDummy250 f)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy252 f)) (synCcompl
              (Class.cab (nb078AlphaDummy249 f)
                (synWrex (nb078AlphaDummy250 f) (Class.cv (nb078AlphaDummy245 f))
                  (Wff.classEq (Class.cv (nb078AlphaDummy249 f))
                    (synCun (synCphi (Class.cv (nb078AlphaDummy250 f)))
                      (synCsn (synC0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy244) ≠ (nb078AlphaDummy248) from (by
                              unfold nb078AlphaDummy248;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0250) 1))))
                          (show (nb078AlphaDummy246 f) ≠ (nb078AlphaDummy250 f) from (by
                              unfold nb078AlphaDummy250;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0252 f) 1))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy244) ≠ (nb078AlphaDummy247) from (by
                                unfold nb078AlphaDummy247;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0250) 0))))
                            (show (nb078AlphaDummy246 f) ≠ (nb078AlphaDummy249 f) from (by
                                unfold nb078AlphaDummy249;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0252 f) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy244) ≠ (nb078AlphaDummy253) from (by
                                  unfold nb078AlphaDummy253;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0254) 0))))
                              (show (nb078AlphaDummy246 f) ≠ (nb078AlphaDummy254 f) from
                                (by
                                  unfold nb078AlphaDummy254;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0255 f) 0))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy244) ≠ (nb078AlphaDummy251) from (by
                                    unfold nb078AlphaDummy251;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0251) 0)))) (show
                                  (nb078AlphaDummy246 f) ≠ (nb078AlphaDummy252 f) from (by
                                    unfold nb078AlphaDummy252;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0253 f)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb078AlphaDummy244))).fv ∪
                              ((Class.cv (nb078AlphaDummy243))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy246 f))).fv ∪
                              ((Class.cv (nb078AlphaDummy245 f))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy248) ≠ (nb078AlphaDummy255) from
                                    (by
                                      unfold nb078AlphaDummy255;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0256)
                                              0)))) (show
                                    (nb078AlphaDummy250 f) ≠ (nb078AlphaDummy257 f) from
                                    (by
                                      unfold nb078AlphaDummy257;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0257 f)
                                              0)))) (TAlphaVar.there (show
                                      (nb078AlphaDummy248) ≠ (nb078AlphaDummy256) from (by
                                        unfold nb078AlphaDummy256;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0256)
                                                1)))) (show (nb078AlphaDummy250 f) ≠
                                        (nb078AlphaDummy258 f) from (by
                                        unfold nb078AlphaDummy258;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0257 f)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb078AlphaDummy248))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb078AlphaDummy250 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy255) ≠ (nb078AlphaDummy262) from (by
          unfold nb078AlphaDummy262;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0260)
                  1)))) (show (nb078AlphaDummy257 f) ≠ (nb078AlphaDummy265 f) from (by
          unfold nb078AlphaDummy265;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0261 f)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy255) ≠ (nb078AlphaDummy261)
        from (by
          unfold nb078AlphaDummy261;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0260)
                  0)))) (show (nb078AlphaDummy257 f) ≠ (nb078AlphaDummy264 f) from (by
          unfold nb078AlphaDummy264;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0261
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy255) ≠ (nb078AlphaDummy259)
        from (by
          unfold nb078AlphaDummy259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0258)
                  0)))) (show (nb078AlphaDummy257 f) ≠ (nb078AlphaDummy260 f) from (by
          unfold nb078AlphaDummy260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0259
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy263), (nb078AlphaDummy266 f)), ((nb078AlphaDummy262),
        (nb078AlphaDummy265 f)), ((nb078AlphaDummy261), (nb078AlphaDummy264 f)),
        ((nb078AlphaDummy259), (nb078AlphaDummy260 f)), ((nb078AlphaDummy255),
        (nb078AlphaDummy257 f)), ((nb078AlphaDummy256), (nb078AlphaDummy258 f)),
        ((nb078AlphaDummy248), (nb078AlphaDummy250 f)), ((nb078AlphaDummy247),
        (nb078AlphaDummy249 f)), ((nb078AlphaDummy253), (nb078AlphaDummy254 f)),
        ((nb078AlphaDummy251), (nb078AlphaDummy252 f)), ((nb078AlphaDummy244),
        (nb078AlphaDummy246 f)), ((nb078AlphaDummy243), (nb078AlphaDummy245 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy262) ≠ (nb078AlphaDummy269) from (by
          unfold
            nb078AlphaDummy269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0264)
                  0)))) (show (nb078AlphaDummy265 f) ≠ (nb078AlphaDummy270 f) from (by
          unfold
            nb078AlphaDummy270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0265
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy262) ≠ (nb078AlphaDummy267)
        from (by
          unfold
            nb078AlphaDummy267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0262)
                  0)))) (show (nb078AlphaDummy265 f) ≠ (nb078AlphaDummy268 f) from (by
          unfold
            nb078AlphaDummy268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0263
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy255))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy257 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy263) ≠
        (nb078AlphaDummy269) from (by
          unfold
            nb078AlphaDummy269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0268)
                  0)))) (show (nb078AlphaDummy266 f) ≠ (nb078AlphaDummy270 f) from (by
          unfold
            nb078AlphaDummy270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0269
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy263) ≠ (nb078AlphaDummy267)
        from (by
          unfold
            nb078AlphaDummy267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0266)
                  0)))) (show (nb078AlphaDummy266 f) ≠ (nb078AlphaDummy268 f) from (by
          unfold
            nb078AlphaDummy268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0267
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy262) ≠ (nb078AlphaDummy269) from (by
          unfold
            nb078AlphaDummy269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0264)
                  0)))) (show (nb078AlphaDummy265 f) ≠ (nb078AlphaDummy270 f) from (by
          unfold
            nb078AlphaDummy270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0265
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy262) ≠ (nb078AlphaDummy267)
        from (by
          unfold
            nb078AlphaDummy267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0262)
                  0)))) (show (nb078AlphaDummy265 f) ≠ (nb078AlphaDummy268 f) from (by
          unfold
            nb078AlphaDummy268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0263
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy255))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy257 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy263) ≠
        (nb078AlphaDummy269) from (by
          unfold
            nb078AlphaDummy269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0268)
                  0)))) (show (nb078AlphaDummy266 f) ≠ (nb078AlphaDummy270 f) from (by
          unfold
            nb078AlphaDummy270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0269
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy263) ≠ (nb078AlphaDummy267)
        from (by
          unfold
            nb078AlphaDummy267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0266)
                  0)))) (show (nb078AlphaDummy266 f) ≠ (nb078AlphaDummy268 f) from (by
          unfold
            nb078AlphaDummy268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0267
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy263), (nb078AlphaDummy266 f)), ((nb078AlphaDummy262),
        (nb078AlphaDummy265 f)), ((nb078AlphaDummy261), (nb078AlphaDummy264 f)),
        ((nb078AlphaDummy259), (nb078AlphaDummy260 f)), ((nb078AlphaDummy255),
        (nb078AlphaDummy257 f)), ((nb078AlphaDummy256), (nb078AlphaDummy258 f)),
        ((nb078AlphaDummy248), (nb078AlphaDummy250 f)), ((nb078AlphaDummy247),
        (nb078AlphaDummy249 f)), ((nb078AlphaDummy253), (nb078AlphaDummy254 f)),
        ((nb078AlphaDummy251), (nb078AlphaDummy252 f)), ((nb078AlphaDummy244),
        (nb078AlphaDummy246 f)), ((nb078AlphaDummy243), (nb078AlphaDummy245 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy255))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy257 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy255))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy257
        f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy262) ≠ (nb078AlphaDummy273) from (by
          unfold
            nb078AlphaDummy273;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0272)
                  0)))) (show (nb078AlphaDummy265 f) ≠ (nb078AlphaDummy274 f) from (by
          unfold
            nb078AlphaDummy274;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0273
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy262) ≠ (nb078AlphaDummy271)
        from (by
          unfold
            nb078AlphaDummy271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0270)
                  0)))) (show (nb078AlphaDummy265 f) ≠ (nb078AlphaDummy272 f) from (by
          unfold
            nb078AlphaDummy272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0271
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy255))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy257 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy262) ≠
        (nb078AlphaDummy273) from (by
          unfold
            nb078AlphaDummy273;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0272)
                  0)))) (show (nb078AlphaDummy265 f) ≠ (nb078AlphaDummy274 f) from (by
          unfold
            nb078AlphaDummy274;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0273
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy262) ≠ (nb078AlphaDummy271)
        from (by
          unfold
            nb078AlphaDummy271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0270)
                  0)))) (show (nb078AlphaDummy265 f) ≠ (nb078AlphaDummy272 f) from (by
          unfold
            nb078AlphaDummy272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0271
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy255))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy257 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy263) ≠ (nb078AlphaDummy275) from (by
          unfold
            nb078AlphaDummy275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0276)
                  0)))) (show (nb078AlphaDummy266 f) ≠ (nb078AlphaDummy276 f) from (by
          unfold
            nb078AlphaDummy276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0277
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy263) ≠ (nb078AlphaDummy271)
        from (by
          unfold
            nb078AlphaDummy271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0274)
                  0)))) (show (nb078AlphaDummy266 f) ≠ (nb078AlphaDummy272 f) from (by
          unfold
            nb078AlphaDummy272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0275
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy263) ≠
        (nb078AlphaDummy275) from (by
          unfold
            nb078AlphaDummy275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0276)
                  0)))) (show (nb078AlphaDummy266 f) ≠ (nb078AlphaDummy276 f) from (by
          unfold
            nb078AlphaDummy276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0277
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy263) ≠ (nb078AlphaDummy271)
        from (by
          unfold
            nb078AlphaDummy271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0274)
                  0)))) (show (nb078AlphaDummy266 f) ≠ (nb078AlphaDummy272 f) from (by
          unfold
            nb078AlphaDummy272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0275
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy255) ≠ (nb078AlphaDummy259) from (by
          unfold nb078AlphaDummy259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0258) 0)))) (show (nb078AlphaDummy257 f) ≠
        (nb078AlphaDummy260 f) from (by
          unfold nb078AlphaDummy260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0259 f) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed [((nb078AlphaDummy259),
        (nb078AlphaDummy260 f)), ((nb078AlphaDummy255), (nb078AlphaDummy257 f)),
        ((nb078AlphaDummy256), (nb078AlphaDummy258 f)), ((nb078AlphaDummy248),
        (nb078AlphaDummy250 f)), ((nb078AlphaDummy247), (nb078AlphaDummy249 f)),
        ((nb078AlphaDummy253), (nb078AlphaDummy254 f)), ((nb078AlphaDummy251),
        (nb078AlphaDummy252 f)), ((nb078AlphaDummy244), (nb078AlphaDummy246 f)),
        ((nb078AlphaDummy243), (nb078AlphaDummy245 f)), ((nb078AlphaDummy000), f),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078AlphaDummy255) ≠
        (nb078AlphaDummy259) from (by
          unfold nb078AlphaDummy259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0258) 0)))) (show (nb078AlphaDummy257 f) ≠
        (nb078AlphaDummy260 f) from (by
          unfold nb078AlphaDummy260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0259 f) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy255) ≠ (nb078AlphaDummy259) from (by
          unfold nb078AlphaDummy259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0258) 0)))) (show (nb078AlphaDummy257 f) ≠
        (nb078AlphaDummy260 f) from (by
          unfold nb078AlphaDummy260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0259 f) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed [((nb078AlphaDummy259),
        (nb078AlphaDummy260 f)), ((nb078AlphaDummy255), (nb078AlphaDummy257 f)),
        ((nb078AlphaDummy256), (nb078AlphaDummy258 f)), ((nb078AlphaDummy248),
        (nb078AlphaDummy250 f)), ((nb078AlphaDummy247), (nb078AlphaDummy249 f)),
        ((nb078AlphaDummy253), (nb078AlphaDummy254 f)), ((nb078AlphaDummy251),
        (nb078AlphaDummy252 f)), ((nb078AlphaDummy244), (nb078AlphaDummy246 f)),
        ((nb078AlphaDummy243), (nb078AlphaDummy245 f)), ((nb078AlphaDummy000), f),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)] (synCnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy244) ≠ (nb078AlphaDummy248) from (by
                              unfold nb078AlphaDummy248;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0250) 1))))
                          (show (nb078AlphaDummy246 f) ≠ (nb078AlphaDummy250 f) from (by
                              unfold nb078AlphaDummy250;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0252 f) 1))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy244) ≠ (nb078AlphaDummy247) from (by
                                unfold nb078AlphaDummy247;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0250) 0))))
                            (show (nb078AlphaDummy246 f) ≠ (nb078AlphaDummy249 f) from (by
                                unfold nb078AlphaDummy249;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0252 f) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy244) ≠ (nb078AlphaDummy253) from (by
                                  unfold nb078AlphaDummy253;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0254) 0))))
                              (show (nb078AlphaDummy246 f) ≠ (nb078AlphaDummy254 f) from
                                (by
                                  unfold nb078AlphaDummy254;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0255 f) 0))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy244) ≠ (nb078AlphaDummy251) from (by
                                    unfold nb078AlphaDummy251;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0251) 0)))) (show
                                  (nb078AlphaDummy246 f) ≠ (nb078AlphaDummy252 f) from (by
                                    unfold nb078AlphaDummy252;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0253 f)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb078AlphaDummy244))).fv ∪
                              ((Class.cv (nb078AlphaDummy243))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy246 f))).fv ∪
                              ((Class.cv (nb078AlphaDummy245 f))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy248) ≠ (nb078AlphaDummy255) from
                                    (by
                                      unfold nb078AlphaDummy255;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0256)
                                              0)))) (show
                                    (nb078AlphaDummy250 f) ≠ (nb078AlphaDummy257 f) from
                                    (by
                                      unfold nb078AlphaDummy257;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0257 f)
                                              0)))) (TAlphaVar.there (show
                                      (nb078AlphaDummy248) ≠ (nb078AlphaDummy256) from (by
                                        unfold nb078AlphaDummy256;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0256)
                                                1)))) (show (nb078AlphaDummy250 f) ≠
                                        (nb078AlphaDummy258 f) from (by
                                        unfold nb078AlphaDummy258;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0257 f)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb078AlphaDummy248))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb078AlphaDummy250 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy255) ≠ (nb078AlphaDummy262) from (by
          unfold nb078AlphaDummy262;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0260)
                  1)))) (show (nb078AlphaDummy257 f) ≠ (nb078AlphaDummy265 f) from (by
          unfold nb078AlphaDummy265;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0261 f)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy255) ≠ (nb078AlphaDummy261)
        from (by
          unfold nb078AlphaDummy261;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0260)
                  0)))) (show (nb078AlphaDummy257 f) ≠ (nb078AlphaDummy264 f) from (by
          unfold nb078AlphaDummy264;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0261
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy255) ≠ (nb078AlphaDummy259)
        from (by
          unfold nb078AlphaDummy259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0258)
                  0)))) (show (nb078AlphaDummy257 f) ≠ (nb078AlphaDummy260 f) from (by
          unfold nb078AlphaDummy260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0259
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy263), (nb078AlphaDummy266 f)), ((nb078AlphaDummy262),
        (nb078AlphaDummy265 f)), ((nb078AlphaDummy261), (nb078AlphaDummy264 f)),
        ((nb078AlphaDummy259), (nb078AlphaDummy260 f)), ((nb078AlphaDummy255),
        (nb078AlphaDummy257 f)), ((nb078AlphaDummy256), (nb078AlphaDummy258 f)),
        ((nb078AlphaDummy248), (nb078AlphaDummy250 f)), ((nb078AlphaDummy247),
        (nb078AlphaDummy249 f)), ((nb078AlphaDummy253), (nb078AlphaDummy254 f)),
        ((nb078AlphaDummy251), (nb078AlphaDummy252 f)), ((nb078AlphaDummy244),
        (nb078AlphaDummy246 f)), ((nb078AlphaDummy243), (nb078AlphaDummy245 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy262) ≠ (nb078AlphaDummy269) from (by
          unfold
            nb078AlphaDummy269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0264)
                  0)))) (show (nb078AlphaDummy265 f) ≠ (nb078AlphaDummy270 f) from (by
          unfold
            nb078AlphaDummy270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0265
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy262) ≠ (nb078AlphaDummy267)
        from (by
          unfold
            nb078AlphaDummy267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0262)
                  0)))) (show (nb078AlphaDummy265 f) ≠ (nb078AlphaDummy268 f) from (by
          unfold
            nb078AlphaDummy268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0263
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy255))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy257 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy263) ≠
        (nb078AlphaDummy269) from (by
          unfold
            nb078AlphaDummy269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0268)
                  0)))) (show (nb078AlphaDummy266 f) ≠ (nb078AlphaDummy270 f) from (by
          unfold
            nb078AlphaDummy270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0269
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy263) ≠ (nb078AlphaDummy267)
        from (by
          unfold
            nb078AlphaDummy267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0266)
                  0)))) (show (nb078AlphaDummy266 f) ≠ (nb078AlphaDummy268 f) from (by
          unfold
            nb078AlphaDummy268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0267
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy262) ≠ (nb078AlphaDummy269) from (by
          unfold
            nb078AlphaDummy269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0264)
                  0)))) (show (nb078AlphaDummy265 f) ≠ (nb078AlphaDummy270 f) from (by
          unfold
            nb078AlphaDummy270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0265
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy262) ≠ (nb078AlphaDummy267)
        from (by
          unfold
            nb078AlphaDummy267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0262)
                  0)))) (show (nb078AlphaDummy265 f) ≠ (nb078AlphaDummy268 f) from (by
          unfold
            nb078AlphaDummy268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0263
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy255))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy257 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy263) ≠
        (nb078AlphaDummy269) from (by
          unfold
            nb078AlphaDummy269;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0268)
                  0)))) (show (nb078AlphaDummy266 f) ≠ (nb078AlphaDummy270 f) from (by
          unfold
            nb078AlphaDummy270;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0269
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy263) ≠ (nb078AlphaDummy267)
        from (by
          unfold
            nb078AlphaDummy267;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0266)
                  0)))) (show (nb078AlphaDummy266 f) ≠ (nb078AlphaDummy268 f) from (by
          unfold
            nb078AlphaDummy268;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0267
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy263), (nb078AlphaDummy266 f)), ((nb078AlphaDummy262),
        (nb078AlphaDummy265 f)), ((nb078AlphaDummy261), (nb078AlphaDummy264 f)),
        ((nb078AlphaDummy259), (nb078AlphaDummy260 f)), ((nb078AlphaDummy255),
        (nb078AlphaDummy257 f)), ((nb078AlphaDummy256), (nb078AlphaDummy258 f)),
        ((nb078AlphaDummy248), (nb078AlphaDummy250 f)), ((nb078AlphaDummy247),
        (nb078AlphaDummy249 f)), ((nb078AlphaDummy253), (nb078AlphaDummy254 f)),
        ((nb078AlphaDummy251), (nb078AlphaDummy252 f)), ((nb078AlphaDummy244),
        (nb078AlphaDummy246 f)), ((nb078AlphaDummy243), (nb078AlphaDummy245 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy255))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy257 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy255))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy257
        f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy262) ≠ (nb078AlphaDummy273) from (by
          unfold
            nb078AlphaDummy273;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0272)
                  0)))) (show (nb078AlphaDummy265 f) ≠ (nb078AlphaDummy274 f) from (by
          unfold
            nb078AlphaDummy274;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0273
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy262) ≠ (nb078AlphaDummy271)
        from (by
          unfold
            nb078AlphaDummy271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0270)
                  0)))) (show (nb078AlphaDummy265 f) ≠ (nb078AlphaDummy272 f) from (by
          unfold
            nb078AlphaDummy272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0271
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy255))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy257 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy262) ≠
        (nb078AlphaDummy273) from (by
          unfold
            nb078AlphaDummy273;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0272)
                  0)))) (show (nb078AlphaDummy265 f) ≠ (nb078AlphaDummy274 f) from (by
          unfold
            nb078AlphaDummy274;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0273
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy262) ≠ (nb078AlphaDummy271)
        from (by
          unfold
            nb078AlphaDummy271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0270)
                  0)))) (show (nb078AlphaDummy265 f) ≠ (nb078AlphaDummy272 f) from (by
          unfold
            nb078AlphaDummy272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0271
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy255))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy257 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy263) ≠ (nb078AlphaDummy275) from (by
          unfold
            nb078AlphaDummy275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0276)
                  0)))) (show (nb078AlphaDummy266 f) ≠ (nb078AlphaDummy276 f) from (by
          unfold
            nb078AlphaDummy276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0277
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy263) ≠ (nb078AlphaDummy271)
        from (by
          unfold
            nb078AlphaDummy271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0274)
                  0)))) (show (nb078AlphaDummy266 f) ≠ (nb078AlphaDummy272 f) from (by
          unfold
            nb078AlphaDummy272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0275
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy263) ≠
        (nb078AlphaDummy275) from (by
          unfold
            nb078AlphaDummy275;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0276)
                  0)))) (show (nb078AlphaDummy266 f) ≠ (nb078AlphaDummy276 f) from (by
          unfold
            nb078AlphaDummy276;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0277
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy263) ≠ (nb078AlphaDummy271)
        from (by
          unfold
            nb078AlphaDummy271;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0274)
                  0)))) (show (nb078AlphaDummy266 f) ≠ (nb078AlphaDummy272 f) from (by
          unfold
            nb078AlphaDummy272;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0275
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy255) ≠ (nb078AlphaDummy259) from (by
          unfold nb078AlphaDummy259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0258) 0)))) (show (nb078AlphaDummy257 f) ≠
        (nb078AlphaDummy260 f) from (by
          unfold nb078AlphaDummy260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0259 f) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed [((nb078AlphaDummy259),
        (nb078AlphaDummy260 f)), ((nb078AlphaDummy255), (nb078AlphaDummy257 f)),
        ((nb078AlphaDummy256), (nb078AlphaDummy258 f)), ((nb078AlphaDummy248),
        (nb078AlphaDummy250 f)), ((nb078AlphaDummy247), (nb078AlphaDummy249 f)),
        ((nb078AlphaDummy253), (nb078AlphaDummy254 f)), ((nb078AlphaDummy251),
        (nb078AlphaDummy252 f)), ((nb078AlphaDummy244), (nb078AlphaDummy246 f)),
        ((nb078AlphaDummy243), (nb078AlphaDummy245 f)), ((nb078AlphaDummy000), f),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078AlphaDummy255) ≠
        (nb078AlphaDummy259) from (by
          unfold nb078AlphaDummy259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0258) 0)))) (show (nb078AlphaDummy257 f) ≠
        (nb078AlphaDummy260 f) from (by
          unfold nb078AlphaDummy260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0259 f) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy255) ≠ (nb078AlphaDummy259) from (by
          unfold nb078AlphaDummy259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0258) 0)))) (show (nb078AlphaDummy257 f) ≠
        (nb078AlphaDummy260 f) from (by
          unfold nb078AlphaDummy260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0259 f) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed [((nb078AlphaDummy259),
        (nb078AlphaDummy260 f)), ((nb078AlphaDummy255), (nb078AlphaDummy257 f)),
        ((nb078AlphaDummy256), (nb078AlphaDummy258 f)), ((nb078AlphaDummy248),
        (nb078AlphaDummy250 f)), ((nb078AlphaDummy247), (nb078AlphaDummy249 f)),
        ((nb078AlphaDummy253), (nb078AlphaDummy254 f)), ((nb078AlphaDummy251),
        (nb078AlphaDummy252 f)), ((nb078AlphaDummy244), (nb078AlphaDummy246 f)),
        ((nb078AlphaDummy243), (nb078AlphaDummy245 f)), ((nb078AlphaDummy000), f),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)] (synCnnc)
        (by simp only [fv_syn_cnnc])))))))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb078SplitAlpha0028 x y f)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb078SplitAlpha0028 x y f)))))))))))

theorem nb078_compact_fv_empty_0240 : (nb078AlphaDummy285) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb078_compact_fv_empty_0241 (g : Var) :
    (nb078AlphaDummy286 g) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb078_compact_fv_empty_0242 : (nb078AlphaDummy283) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb078_compact_fv_empty_0243 (g : Var) :
    (nb078AlphaDummy284 g) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb078_compact_fv_empty_0244 : (nb078AlphaDummy001) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
