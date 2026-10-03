/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C068C001Block010

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C068C001Part043`. -/


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
noncomputable def nb068_split_alpha_0108 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_450), (nb068_alpha_dummy_452 f)),
        ((nb068_alpha_dummy_449), (nb068_alpha_dummy_451 f)),
        ((nb068_alpha_dummy_479), (nb068_alpha_dummy_480 f)),
        ((nb068_alpha_dummy_453), (nb068_alpha_dummy_454 f)),
        ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
        ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
        ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
        ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
        ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
        ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
        ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
        ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
        ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb068_alpha_dummy_450))
            (Class.cv (nb068_alpha_dummy_407))) (Wff.classEq (Class.cv (nb068_alpha_dummy_449))
            (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_450))) (syn_csn (syn_c0c))))))
      (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb068_alpha_dummy_452 f))
            (Class.cv (nb068_alpha_dummy_409 f)))
          (Wff.classEq (Class.cv (nb068_alpha_dummy_451 f))
            (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_452 f))) (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there
            (show (nb068_alpha_dummy_407) ≠ (nb068_alpha_dummy_450) from (by
                unfold nb068_alpha_dummy_450;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0490) 1))))
            (show (nb068_alpha_dummy_409 f) ≠ (nb068_alpha_dummy_452 f) from (by
                unfold nb068_alpha_dummy_452;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0492 f) 1))))
            (TAlphaVar.there (show (nb068_alpha_dummy_407) ≠ (nb068_alpha_dummy_449) from (by
                  unfold nb068_alpha_dummy_449;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0490) 0))))
              (show (nb068_alpha_dummy_409 f) ≠ (nb068_alpha_dummy_451 f) from (by
                  unfold nb068_alpha_dummy_451;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0492 f) 0))))
              (TAlphaVar.there (show (nb068_alpha_dummy_407) ≠ (nb068_alpha_dummy_479) from (by
                    unfold nb068_alpha_dummy_479;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0494) 0))))
                (show (nb068_alpha_dummy_409 f) ≠ (nb068_alpha_dummy_480 f) from (by
                    unfold nb068_alpha_dummy_480;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0495 f) 0))))
                (TAlphaVar.there (show (nb068_alpha_dummy_407) ≠ (nb068_alpha_dummy_453) from
                    (by
                      unfold nb068_alpha_dummy_453;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0491) 0))))
                  (show (nb068_alpha_dummy_409 f) ≠ (nb068_alpha_dummy_454 f) from (by
                      unfold nb068_alpha_dummy_454;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0493 f) 0))))
                  (TAlphaVar.there (freshVar_injective
                      (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv) (by decide))
                    (freshVar_injective (((syn_ccnv (Class.cv f))).fv) (by decide))
                    (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_408))).fv ∪
                ((Class.cv (nb068_alpha_dummy_407))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb068_alpha_dummy_410 f))).fv ∪
                ((Class.cv (nb068_alpha_dummy_409 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb068_alpha_dummy_450) ≠ (nb068_alpha_dummy_457) from (by
                                        unfold nb068_alpha_dummy_457;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0468)
                                                0)))) (show (nb068_alpha_dummy_452 f) ≠
                                        (nb068_alpha_dummy_459 f) from (by
                                        unfold nb068_alpha_dummy_459;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0469 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068_alpha_dummy_450) ≠ (nb068_alpha_dummy_458) from
                                        (by
                                          unfold nb068_alpha_dummy_458;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0468)
                                                  1)))) (show (nb068_alpha_dummy_452 f) ≠
        (nb068_alpha_dummy_460 f) from (by
                                          unfold nb068_alpha_dummy_460;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0469 f) 1))))
                                      (TAlphaVar.there (show (nb068_alpha_dummy_450) ≠
        (nb068_alpha_dummy_483) from (by
          unfold nb068_alpha_dummy_483;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0498) 0)))) (show (nb068_alpha_dummy_452 f) ≠
        (nb068_alpha_dummy_484 f) from (by
          unfold nb068_alpha_dummy_484;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0499 f) 0)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_450) ≠ (nb068_alpha_dummy_481) from (by
          unfold nb068_alpha_dummy_481;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0496) 0)))) (show (nb068_alpha_dummy_452 f) ≠
        (nb068_alpha_dummy_482 f) from (by
          unfold nb068_alpha_dummy_482;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0497 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb068_alpha_dummy_450))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb068_alpha_dummy_452 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _)))
                                (TAlphaClass.cab (nb068_split_alpha_0107 x y f)))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb068_alpha_dummy_450) ≠ (nb068_alpha_dummy_457) from (by
                                        unfold nb068_alpha_dummy_457;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0468)
                                                0)))) (show (nb068_alpha_dummy_452 f) ≠
                                        (nb068_alpha_dummy_459 f) from (by
                                        unfold nb068_alpha_dummy_459;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0469 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068_alpha_dummy_450) ≠ (nb068_alpha_dummy_458) from
                                        (by
                                          unfold nb068_alpha_dummy_458;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0468)
                                                  1)))) (show (nb068_alpha_dummy_452 f) ≠
        (nb068_alpha_dummy_460 f) from (by
                                          unfold nb068_alpha_dummy_460;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0469 f) 1))))
                                      (TAlphaVar.there (show (nb068_alpha_dummy_450) ≠
        (nb068_alpha_dummy_483) from (by
          unfold nb068_alpha_dummy_483;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0498) 0)))) (show (nb068_alpha_dummy_452 f) ≠
        (nb068_alpha_dummy_484 f) from (by
          unfold nb068_alpha_dummy_484;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0499 f) 0)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_450) ≠ (nb068_alpha_dummy_481) from (by
          unfold nb068_alpha_dummy_481;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0496) 0)))) (show (nb068_alpha_dummy_452 f) ≠
        (nb068_alpha_dummy_482 f) from (by
          unfold nb068_alpha_dummy_482;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0497 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb068_alpha_dummy_450))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb068_alpha_dummy_452 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _)))
                                (TAlphaClass.cab (nb068_split_alpha_0107 x y f)))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb068_alpha_dummy_481), (nb068_alpha_dummy_482 f)),
                    ((nb068_alpha_dummy_450), (nb068_alpha_dummy_452 f)),
                    ((nb068_alpha_dummy_449), (nb068_alpha_dummy_451 f)),
                    ((nb068_alpha_dummy_479), (nb068_alpha_dummy_480 f)),
                    ((nb068_alpha_dummy_453), (nb068_alpha_dummy_454 f)),
                    ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
                    ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
                    ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
                    ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
                    ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
                    ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
                    ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
                    ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
                    ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
                    ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                    ((nb068_alpha_dummy_001), x),
                    ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                  (syn_ccompl (syn_csn (syn_c0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

@[expose]
noncomputable def nb068_split_alpha_0109 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_147), (nb068_alpha_dummy_150 f)),
        ((nb068_alpha_dummy_146), (nb068_alpha_dummy_149 f)),
        ((nb068_alpha_dummy_145), (nb068_alpha_dummy_148 f)),
        ((nb068_alpha_dummy_143), (nb068_alpha_dummy_144 f)),
        ((nb068_alpha_dummy_139), (nb068_alpha_dummy_141 f)),
        ((nb068_alpha_dummy_140), (nb068_alpha_dummy_142 f)),
        ((nb068_alpha_dummy_132), (nb068_alpha_dummy_134 f)),
        ((nb068_alpha_dummy_131), (nb068_alpha_dummy_133 f)),
        ((nb068_alpha_dummy_137), (nb068_alpha_dummy_138 f)),
        ((nb068_alpha_dummy_135), (nb068_alpha_dummy_136 f)),
        ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
        ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
        ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
        ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
        ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
        ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
        ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
        ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
        ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
        ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
        ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
        ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb068_alpha_dummy_146)) (Class.cv (nb068_alpha_dummy_147)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_145))
            (syn_cun (Class.cv (nb068_alpha_dummy_146)) (Class.cv (nb068_alpha_dummy_147))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_149 f))
            (Class.cv (nb068_alpha_dummy_150 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_148 f))
            (syn_cun (Class.cv (nb068_alpha_dummy_149 f))
              (Class.cv (nb068_alpha_dummy_150 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_146) ≠ (nb068_alpha_dummy_153) from (by
                              unfold nb068_alpha_dummy_153;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0140) 0))))
                          (show (nb068_alpha_dummy_149 f) ≠ (nb068_alpha_dummy_154 f) from (by
                              unfold nb068_alpha_dummy_154;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0141 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_146) ≠ (nb068_alpha_dummy_151) from (by
                                unfold nb068_alpha_dummy_151;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0138) 0))))
                            (show (nb068_alpha_dummy_149 f) ≠ (nb068_alpha_dummy_152 f) from (by
                                unfold nb068_alpha_dummy_152;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0139 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_147) ≠ (nb068_alpha_dummy_153) from (by
                              unfold nb068_alpha_dummy_153;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0144) 0))))
                          (show (nb068_alpha_dummy_150 f) ≠ (nb068_alpha_dummy_154 f) from (by
                              unfold nb068_alpha_dummy_154;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0145 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_147) ≠ (nb068_alpha_dummy_151) from (by
                                unfold nb068_alpha_dummy_151;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0142) 0))))
                            (show (nb068_alpha_dummy_150 f) ≠ (nb068_alpha_dummy_152 f) from (by
                                unfold nb068_alpha_dummy_152;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0143 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_146) ≠ (nb068_alpha_dummy_153) from (by
                              unfold nb068_alpha_dummy_153;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0140) 0))))
                          (show (nb068_alpha_dummy_149 f) ≠ (nb068_alpha_dummy_154 f) from (by
                              unfold nb068_alpha_dummy_154;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0141 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_146) ≠ (nb068_alpha_dummy_151) from (by
                                unfold nb068_alpha_dummy_151;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0138) 0))))
                            (show (nb068_alpha_dummy_149 f) ≠ (nb068_alpha_dummy_152 f) from (by
                                unfold nb068_alpha_dummy_152;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0139 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_147) ≠ (nb068_alpha_dummy_153) from (by
                              unfold nb068_alpha_dummy_153;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0144) 0))))
                          (show (nb068_alpha_dummy_150 f) ≠ (nb068_alpha_dummy_154 f) from (by
                              unfold nb068_alpha_dummy_154;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0145 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_147) ≠ (nb068_alpha_dummy_151) from (by
                                unfold nb068_alpha_dummy_151;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0142) 0))))
                            (show (nb068_alpha_dummy_150 f) ≠ (nb068_alpha_dummy_152 f) from (by
                                unfold nb068_alpha_dummy_152;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0143 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb068_alpha_dummy_147), (nb068_alpha_dummy_150 f)),
          ((nb068_alpha_dummy_146), (nb068_alpha_dummy_149 f)),
          ((nb068_alpha_dummy_145), (nb068_alpha_dummy_148 f)),
          ((nb068_alpha_dummy_143), (nb068_alpha_dummy_144 f)),
          ((nb068_alpha_dummy_139), (nb068_alpha_dummy_141 f)),
          ((nb068_alpha_dummy_140), (nb068_alpha_dummy_142 f)),
          ((nb068_alpha_dummy_132), (nb068_alpha_dummy_134 f)),
          ((nb068_alpha_dummy_131), (nb068_alpha_dummy_133 f)),
          ((nb068_alpha_dummy_137), (nb068_alpha_dummy_138 f)),
          ((nb068_alpha_dummy_135), (nb068_alpha_dummy_136 f)),
          ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
          ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
          ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
          ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
          ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
          ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
          ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
          ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
          ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
          ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
          ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
          ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
          ((nb068_alpha_dummy_001), x),
          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_146) ≠ (nb068_alpha_dummy_157) from (by
                                unfold nb068_alpha_dummy_157;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0148) 0))))
                            (show (nb068_alpha_dummy_149 f) ≠ (nb068_alpha_dummy_158 f) from (by
                                unfold nb068_alpha_dummy_158;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0149 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_146) ≠ (nb068_alpha_dummy_155) from (by
                                  unfold nb068_alpha_dummy_155;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0146) 0))))
                              (show (nb068_alpha_dummy_149 f) ≠ (nb068_alpha_dummy_156 f) from
                                (by
                                  unfold nb068_alpha_dummy_156;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0147 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_146) ≠ (nb068_alpha_dummy_157) from (by
                                unfold nb068_alpha_dummy_157;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0148) 0))))
                            (show (nb068_alpha_dummy_149 f) ≠ (nb068_alpha_dummy_158 f) from (by
                                unfold nb068_alpha_dummy_158;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0149 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_146) ≠ (nb068_alpha_dummy_155) from (by
                                  unfold nb068_alpha_dummy_155;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0146) 0))))
                              (show (nb068_alpha_dummy_149 f) ≠ (nb068_alpha_dummy_156 f) from
                                (by
                                  unfold nb068_alpha_dummy_156;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0147 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_147) ≠ (nb068_alpha_dummy_159) from (by
                                unfold nb068_alpha_dummy_159;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0152) 0))))
                            (show (nb068_alpha_dummy_150 f) ≠ (nb068_alpha_dummy_160 f) from (by
                                unfold nb068_alpha_dummy_160;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0153 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_147) ≠ (nb068_alpha_dummy_155) from (by
                                  unfold nb068_alpha_dummy_155;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0150) 0))))
                              (show (nb068_alpha_dummy_150 f) ≠ (nb068_alpha_dummy_156 f) from
                                (by
                                  unfold nb068_alpha_dummy_156;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0151 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_147) ≠ (nb068_alpha_dummy_159) from (by
                                unfold nb068_alpha_dummy_159;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0152) 0))))
                            (show (nb068_alpha_dummy_150 f) ≠ (nb068_alpha_dummy_160 f) from (by
                                unfold nb068_alpha_dummy_160;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0153 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_147) ≠ (nb068_alpha_dummy_155) from (by
                                  unfold nb068_alpha_dummy_155;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0150) 0))))
                              (show (nb068_alpha_dummy_150 f) ≠ (nb068_alpha_dummy_156 f) from
                                (by
                                  unfold nb068_alpha_dummy_156;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0151 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb068_split_alpha_0110 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_143), (nb068_alpha_dummy_144 f)),
        ((nb068_alpha_dummy_139), (nb068_alpha_dummy_141 f)),
        ((nb068_alpha_dummy_140), (nb068_alpha_dummy_142 f)),
        ((nb068_alpha_dummy_132), (nb068_alpha_dummy_134 f)),
        ((nb068_alpha_dummy_131), (nb068_alpha_dummy_133 f)),
        ((nb068_alpha_dummy_137), (nb068_alpha_dummy_138 f)),
        ((nb068_alpha_dummy_135), (nb068_alpha_dummy_136 f)),
        ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
        ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
        ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
        ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
        ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
        ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
        ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
        ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
        ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
        ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
        ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
        ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb068_alpha_dummy_143))
              (syn_cplc (Class.cv (nb068_alpha_dummy_139)) (syn_c1c)))
            (Wff.classMem (Class.cv (nb068_alpha_dummy_139)) (syn_cnnc)))) (syn_wa
          (Wff.classMem (Class.cv (nb068_alpha_dummy_143)) (Class.cv (nb068_alpha_dummy_139)))
          (Wff.neg (Wff.classMem (Class.cv (nb068_alpha_dummy_139)) (syn_cnnc)))))
      (Wff.imp (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb068_alpha_dummy_144 f))
              (syn_cplc (Class.cv (nb068_alpha_dummy_141 f)) (syn_c1c)))
            (Wff.classMem (Class.cv (nb068_alpha_dummy_141 f)) (syn_cnnc)))) (syn_wa
          (Wff.classMem (Class.cv (nb068_alpha_dummy_144 f))
            (Class.cv (nb068_alpha_dummy_141 f)))
          (Wff.neg (Wff.classMem (Class.cv (nb068_alpha_dummy_141 f)) (syn_cnnc))))) :=
  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068_alpha_dummy_139) ≠ (nb068_alpha_dummy_146) from (by
                          unfold nb068_alpha_dummy_146;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0136) 1))))
                      (show (nb068_alpha_dummy_141 f) ≠ (nb068_alpha_dummy_149 f) from (by
                          unfold nb068_alpha_dummy_149;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0137 f) 1))))
                      (TAlphaVar.there
                        (show (nb068_alpha_dummy_139) ≠ (nb068_alpha_dummy_145) from (by
                            unfold nb068_alpha_dummy_145;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0136) 0))))
                        (show (nb068_alpha_dummy_141 f) ≠ (nb068_alpha_dummy_148 f) from (by
                            unfold nb068_alpha_dummy_148;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0137 f) 0))))
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_139) ≠ (nb068_alpha_dummy_143) from (by
                              unfold nb068_alpha_dummy_143;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0134) 0))))
                          (show (nb068_alpha_dummy_141 f) ≠ (nb068_alpha_dummy_144 f) from (by
                              unfold nb068_alpha_dummy_144;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
                          (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb068_alpha_dummy_147), (nb068_alpha_dummy_150 f)),
                          ((nb068_alpha_dummy_146), (nb068_alpha_dummy_149 f)),
                          ((nb068_alpha_dummy_145), (nb068_alpha_dummy_148 f)),
                          ((nb068_alpha_dummy_143), (nb068_alpha_dummy_144 f)),
                          ((nb068_alpha_dummy_139), (nb068_alpha_dummy_141 f)),
                          ((nb068_alpha_dummy_140), (nb068_alpha_dummy_142 f)),
                          ((nb068_alpha_dummy_132), (nb068_alpha_dummy_134 f)),
                          ((nb068_alpha_dummy_131), (nb068_alpha_dummy_133 f)),
                          ((nb068_alpha_dummy_137), (nb068_alpha_dummy_138 f)),
                          ((nb068_alpha_dummy_135), (nb068_alpha_dummy_136 f)),
                          ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
                          ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
                          ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
                          ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
                          ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
                          ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
                          ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
                          ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
                          ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
                          ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
                          ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
                          ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
                          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                          ((nb068_alpha_dummy_001), x),
                          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                        (syn_c1c) (by simp only [fv_syn_c1c])))
                    (TAlphaWff.neg (nb068_split_alpha_0109 x y f)))))))) (TAlphaWff.classMem
          (TAlphaClass.cv (TAlphaVar.there
              (show (nb068_alpha_dummy_139) ≠ (nb068_alpha_dummy_143) from (by
                  unfold nb068_alpha_dummy_143;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0134) 0))))
              (show (nb068_alpha_dummy_141 f) ≠ (nb068_alpha_dummy_144 f) from (by
                  unfold nb068_alpha_dummy_144;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
            [((nb068_alpha_dummy_143), (nb068_alpha_dummy_144 f)),
              ((nb068_alpha_dummy_139), (nb068_alpha_dummy_141 f)),
              ((nb068_alpha_dummy_140), (nb068_alpha_dummy_142 f)),
              ((nb068_alpha_dummy_132), (nb068_alpha_dummy_134 f)),
              ((nb068_alpha_dummy_131), (nb068_alpha_dummy_133 f)),
              ((nb068_alpha_dummy_137), (nb068_alpha_dummy_138 f)),
              ((nb068_alpha_dummy_135), (nb068_alpha_dummy_136 f)),
              ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
              ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
              ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
              ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
              ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
              ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
              ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
              ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
              ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
              ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
              ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
              ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
              ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
              ((nb068_alpha_dummy_001), x),
              ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
          (TAlphaVar.there (show (nb068_alpha_dummy_139) ≠ (nb068_alpha_dummy_143) from (by
                unfold nb068_alpha_dummy_143;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0134) 0))))
            (show (nb068_alpha_dummy_141 f) ≠ (nb068_alpha_dummy_144 f) from (by
                unfold nb068_alpha_dummy_144;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
            (TAlphaVar.there (show (nb068_alpha_dummy_139) ≠ (nb068_alpha_dummy_143) from (by
                  unfold nb068_alpha_dummy_143;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0134) 0))))
              (show (nb068_alpha_dummy_141 f) ≠ (nb068_alpha_dummy_144 f) from (by
                  unfold nb068_alpha_dummy_144;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
            [((nb068_alpha_dummy_143), (nb068_alpha_dummy_144 f)),
              ((nb068_alpha_dummy_139), (nb068_alpha_dummy_141 f)),
              ((nb068_alpha_dummy_140), (nb068_alpha_dummy_142 f)),
              ((nb068_alpha_dummy_132), (nb068_alpha_dummy_134 f)),
              ((nb068_alpha_dummy_131), (nb068_alpha_dummy_133 f)),
              ((nb068_alpha_dummy_137), (nb068_alpha_dummy_138 f)),
              ((nb068_alpha_dummy_135), (nb068_alpha_dummy_136 f)),
              ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
              ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
              ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
              ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
              ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
              ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
              ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
              ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
              ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
              ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
              ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
              ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
              ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
              ((nb068_alpha_dummy_001), x),
              ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part044`. -/


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
noncomputable def nb068_split_alpha_0111 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_147), (nb068_alpha_dummy_150 f)),
        ((nb068_alpha_dummy_146), (nb068_alpha_dummy_149 f)),
        ((nb068_alpha_dummy_145), (nb068_alpha_dummy_148 f)),
        ((nb068_alpha_dummy_143), (nb068_alpha_dummy_144 f)),
        ((nb068_alpha_dummy_139), (nb068_alpha_dummy_141 f)),
        ((nb068_alpha_dummy_140), (nb068_alpha_dummy_142 f)),
        ((nb068_alpha_dummy_165), (nb068_alpha_dummy_166 f)),
        ((nb068_alpha_dummy_163), (nb068_alpha_dummy_164 f)),
        ((nb068_alpha_dummy_132), (nb068_alpha_dummy_134 f)),
        ((nb068_alpha_dummy_131), (nb068_alpha_dummy_133 f)),
        ((nb068_alpha_dummy_161), (nb068_alpha_dummy_162 f)),
        ((nb068_alpha_dummy_135), (nb068_alpha_dummy_136 f)),
        ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
        ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
        ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
        ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
        ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
        ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
        ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
        ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
        ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
        ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
        ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
        ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb068_alpha_dummy_146)) (Class.cv (nb068_alpha_dummy_147)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_145))
            (syn_cun (Class.cv (nb068_alpha_dummy_146)) (Class.cv (nb068_alpha_dummy_147))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_149 f))
            (Class.cv (nb068_alpha_dummy_150 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_148 f))
            (syn_cun (Class.cv (nb068_alpha_dummy_149 f))
              (Class.cv (nb068_alpha_dummy_150 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_146) ≠ (nb068_alpha_dummy_153) from (by
                              unfold nb068_alpha_dummy_153;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0140) 0))))
                          (show (nb068_alpha_dummy_149 f) ≠ (nb068_alpha_dummy_154 f) from (by
                              unfold nb068_alpha_dummy_154;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0141 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_146) ≠ (nb068_alpha_dummy_151) from (by
                                unfold nb068_alpha_dummy_151;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0138) 0))))
                            (show (nb068_alpha_dummy_149 f) ≠ (nb068_alpha_dummy_152 f) from (by
                                unfold nb068_alpha_dummy_152;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0139 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_147) ≠ (nb068_alpha_dummy_153) from (by
                              unfold nb068_alpha_dummy_153;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0144) 0))))
                          (show (nb068_alpha_dummy_150 f) ≠ (nb068_alpha_dummy_154 f) from (by
                              unfold nb068_alpha_dummy_154;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0145 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_147) ≠ (nb068_alpha_dummy_151) from (by
                                unfold nb068_alpha_dummy_151;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0142) 0))))
                            (show (nb068_alpha_dummy_150 f) ≠ (nb068_alpha_dummy_152 f) from (by
                                unfold nb068_alpha_dummy_152;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0143 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_146) ≠ (nb068_alpha_dummy_153) from (by
                              unfold nb068_alpha_dummy_153;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0140) 0))))
                          (show (nb068_alpha_dummy_149 f) ≠ (nb068_alpha_dummy_154 f) from (by
                              unfold nb068_alpha_dummy_154;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0141 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_146) ≠ (nb068_alpha_dummy_151) from (by
                                unfold nb068_alpha_dummy_151;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0138) 0))))
                            (show (nb068_alpha_dummy_149 f) ≠ (nb068_alpha_dummy_152 f) from (by
                                unfold nb068_alpha_dummy_152;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0139 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_147) ≠ (nb068_alpha_dummy_153) from (by
                              unfold nb068_alpha_dummy_153;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0144) 0))))
                          (show (nb068_alpha_dummy_150 f) ≠ (nb068_alpha_dummy_154 f) from (by
                              unfold nb068_alpha_dummy_154;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0145 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_147) ≠ (nb068_alpha_dummy_151) from (by
                                unfold nb068_alpha_dummy_151;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0142) 0))))
                            (show (nb068_alpha_dummy_150 f) ≠ (nb068_alpha_dummy_152 f) from (by
                                unfold nb068_alpha_dummy_152;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0143 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb068_alpha_dummy_147), (nb068_alpha_dummy_150 f)),
          ((nb068_alpha_dummy_146), (nb068_alpha_dummy_149 f)),
          ((nb068_alpha_dummy_145), (nb068_alpha_dummy_148 f)),
          ((nb068_alpha_dummy_143), (nb068_alpha_dummy_144 f)),
          ((nb068_alpha_dummy_139), (nb068_alpha_dummy_141 f)),
          ((nb068_alpha_dummy_140), (nb068_alpha_dummy_142 f)),
          ((nb068_alpha_dummy_165), (nb068_alpha_dummy_166 f)),
          ((nb068_alpha_dummy_163), (nb068_alpha_dummy_164 f)),
          ((nb068_alpha_dummy_132), (nb068_alpha_dummy_134 f)),
          ((nb068_alpha_dummy_131), (nb068_alpha_dummy_133 f)),
          ((nb068_alpha_dummy_161), (nb068_alpha_dummy_162 f)),
          ((nb068_alpha_dummy_135), (nb068_alpha_dummy_136 f)),
          ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
          ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
          ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
          ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
          ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
          ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
          ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
          ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
          ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
          ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
          ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
          ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
          ((nb068_alpha_dummy_001), x),
          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_146) ≠ (nb068_alpha_dummy_157) from (by
                                unfold nb068_alpha_dummy_157;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0148) 0))))
                            (show (nb068_alpha_dummy_149 f) ≠ (nb068_alpha_dummy_158 f) from (by
                                unfold nb068_alpha_dummy_158;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0149 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_146) ≠ (nb068_alpha_dummy_155) from (by
                                  unfold nb068_alpha_dummy_155;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0146) 0))))
                              (show (nb068_alpha_dummy_149 f) ≠ (nb068_alpha_dummy_156 f) from
                                (by
                                  unfold nb068_alpha_dummy_156;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0147 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_146) ≠ (nb068_alpha_dummy_157) from (by
                                unfold nb068_alpha_dummy_157;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0148) 0))))
                            (show (nb068_alpha_dummy_149 f) ≠ (nb068_alpha_dummy_158 f) from (by
                                unfold nb068_alpha_dummy_158;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0149 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_146) ≠ (nb068_alpha_dummy_155) from (by
                                  unfold nb068_alpha_dummy_155;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0146) 0))))
                              (show (nb068_alpha_dummy_149 f) ≠ (nb068_alpha_dummy_156 f) from
                                (by
                                  unfold nb068_alpha_dummy_156;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0147 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_147) ≠ (nb068_alpha_dummy_159) from (by
                                unfold nb068_alpha_dummy_159;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0152) 0))))
                            (show (nb068_alpha_dummy_150 f) ≠ (nb068_alpha_dummy_160 f) from (by
                                unfold nb068_alpha_dummy_160;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0153 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_147) ≠ (nb068_alpha_dummy_155) from (by
                                  unfold nb068_alpha_dummy_155;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0150) 0))))
                              (show (nb068_alpha_dummy_150 f) ≠ (nb068_alpha_dummy_156 f) from
                                (by
                                  unfold nb068_alpha_dummy_156;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0151 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_147) ≠ (nb068_alpha_dummy_159) from (by
                                unfold nb068_alpha_dummy_159;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0152) 0))))
                            (show (nb068_alpha_dummy_150 f) ≠ (nb068_alpha_dummy_160 f) from (by
                                unfold nb068_alpha_dummy_160;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0153 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_147) ≠ (nb068_alpha_dummy_155) from (by
                                  unfold nb068_alpha_dummy_155;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0150) 0))))
                              (show (nb068_alpha_dummy_150 f) ≠ (nb068_alpha_dummy_156 f) from
                                (by
                                  unfold nb068_alpha_dummy_156;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0151 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb068_split_alpha_0112 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_143), (nb068_alpha_dummy_144 f)),
        ((nb068_alpha_dummy_139), (nb068_alpha_dummy_141 f)),
        ((nb068_alpha_dummy_140), (nb068_alpha_dummy_142 f)),
        ((nb068_alpha_dummy_165), (nb068_alpha_dummy_166 f)),
        ((nb068_alpha_dummy_163), (nb068_alpha_dummy_164 f)),
        ((nb068_alpha_dummy_132), (nb068_alpha_dummy_134 f)),
        ((nb068_alpha_dummy_131), (nb068_alpha_dummy_133 f)),
        ((nb068_alpha_dummy_161), (nb068_alpha_dummy_162 f)),
        ((nb068_alpha_dummy_135), (nb068_alpha_dummy_136 f)),
        ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
        ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
        ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
        ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
        ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
        ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
        ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
        ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
        ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
        ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
        ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
        ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb068_alpha_dummy_143))
              (syn_cplc (Class.cv (nb068_alpha_dummy_139)) (syn_c1c)))
            (Wff.classMem (Class.cv (nb068_alpha_dummy_139)) (syn_cnnc)))) (syn_wa
          (Wff.classMem (Class.cv (nb068_alpha_dummy_143)) (Class.cv (nb068_alpha_dummy_139)))
          (Wff.neg (Wff.classMem (Class.cv (nb068_alpha_dummy_139)) (syn_cnnc)))))
      (Wff.imp (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb068_alpha_dummy_144 f))
              (syn_cplc (Class.cv (nb068_alpha_dummy_141 f)) (syn_c1c)))
            (Wff.classMem (Class.cv (nb068_alpha_dummy_141 f)) (syn_cnnc)))) (syn_wa
          (Wff.classMem (Class.cv (nb068_alpha_dummy_144 f))
            (Class.cv (nb068_alpha_dummy_141 f)))
          (Wff.neg (Wff.classMem (Class.cv (nb068_alpha_dummy_141 f)) (syn_cnnc))))) :=
  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068_alpha_dummy_139) ≠ (nb068_alpha_dummy_146) from (by
                          unfold nb068_alpha_dummy_146;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0136) 1))))
                      (show (nb068_alpha_dummy_141 f) ≠ (nb068_alpha_dummy_149 f) from (by
                          unfold nb068_alpha_dummy_149;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0137 f) 1))))
                      (TAlphaVar.there
                        (show (nb068_alpha_dummy_139) ≠ (nb068_alpha_dummy_145) from (by
                            unfold nb068_alpha_dummy_145;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0136) 0))))
                        (show (nb068_alpha_dummy_141 f) ≠ (nb068_alpha_dummy_148 f) from (by
                            unfold nb068_alpha_dummy_148;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0137 f) 0))))
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_139) ≠ (nb068_alpha_dummy_143) from (by
                              unfold nb068_alpha_dummy_143;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0134) 0))))
                          (show (nb068_alpha_dummy_141 f) ≠ (nb068_alpha_dummy_144 f) from (by
                              unfold nb068_alpha_dummy_144;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
                          (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb068_alpha_dummy_147), (nb068_alpha_dummy_150 f)),
                          ((nb068_alpha_dummy_146), (nb068_alpha_dummy_149 f)),
                          ((nb068_alpha_dummy_145), (nb068_alpha_dummy_148 f)),
                          ((nb068_alpha_dummy_143), (nb068_alpha_dummy_144 f)),
                          ((nb068_alpha_dummy_139), (nb068_alpha_dummy_141 f)),
                          ((nb068_alpha_dummy_140), (nb068_alpha_dummy_142 f)),
                          ((nb068_alpha_dummy_165), (nb068_alpha_dummy_166 f)),
                          ((nb068_alpha_dummy_163), (nb068_alpha_dummy_164 f)),
                          ((nb068_alpha_dummy_132), (nb068_alpha_dummy_134 f)),
                          ((nb068_alpha_dummy_131), (nb068_alpha_dummy_133 f)),
                          ((nb068_alpha_dummy_161), (nb068_alpha_dummy_162 f)),
                          ((nb068_alpha_dummy_135), (nb068_alpha_dummy_136 f)),
                          ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
                          ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
                          ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
                          ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
                          ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
                          ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
                          ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
                          ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
                          ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
                          ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
                          ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
                          ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
                          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                          ((nb068_alpha_dummy_001), x),
                          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                        (syn_c1c) (by simp only [fv_syn_c1c])))
                    (TAlphaWff.neg (nb068_split_alpha_0111 x y f)))))))) (TAlphaWff.classMem
          (TAlphaClass.cv (TAlphaVar.there
              (show (nb068_alpha_dummy_139) ≠ (nb068_alpha_dummy_143) from (by
                  unfold nb068_alpha_dummy_143;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0134) 0))))
              (show (nb068_alpha_dummy_141 f) ≠ (nb068_alpha_dummy_144 f) from (by
                  unfold nb068_alpha_dummy_144;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
            [((nb068_alpha_dummy_143), (nb068_alpha_dummy_144 f)),
              ((nb068_alpha_dummy_139), (nb068_alpha_dummy_141 f)),
              ((nb068_alpha_dummy_140), (nb068_alpha_dummy_142 f)),
              ((nb068_alpha_dummy_165), (nb068_alpha_dummy_166 f)),
              ((nb068_alpha_dummy_163), (nb068_alpha_dummy_164 f)),
              ((nb068_alpha_dummy_132), (nb068_alpha_dummy_134 f)),
              ((nb068_alpha_dummy_131), (nb068_alpha_dummy_133 f)),
              ((nb068_alpha_dummy_161), (nb068_alpha_dummy_162 f)),
              ((nb068_alpha_dummy_135), (nb068_alpha_dummy_136 f)),
              ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
              ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
              ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
              ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
              ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
              ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
              ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
              ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
              ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
              ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
              ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
              ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
              ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
              ((nb068_alpha_dummy_001), x),
              ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
          (TAlphaVar.there (show (nb068_alpha_dummy_139) ≠ (nb068_alpha_dummy_143) from (by
                unfold nb068_alpha_dummy_143;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0134) 0))))
            (show (nb068_alpha_dummy_141 f) ≠ (nb068_alpha_dummy_144 f) from (by
                unfold nb068_alpha_dummy_144;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
            (TAlphaVar.there (show (nb068_alpha_dummy_139) ≠ (nb068_alpha_dummy_143) from (by
                  unfold nb068_alpha_dummy_143;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0134) 0))))
              (show (nb068_alpha_dummy_141 f) ≠ (nb068_alpha_dummy_144 f) from (by
                  unfold nb068_alpha_dummy_144;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
            [((nb068_alpha_dummy_143), (nb068_alpha_dummy_144 f)),
              ((nb068_alpha_dummy_139), (nb068_alpha_dummy_141 f)),
              ((nb068_alpha_dummy_140), (nb068_alpha_dummy_142 f)),
              ((nb068_alpha_dummy_165), (nb068_alpha_dummy_166 f)),
              ((nb068_alpha_dummy_163), (nb068_alpha_dummy_164 f)),
              ((nb068_alpha_dummy_132), (nb068_alpha_dummy_134 f)),
              ((nb068_alpha_dummy_131), (nb068_alpha_dummy_133 f)),
              ((nb068_alpha_dummy_161), (nb068_alpha_dummy_162 f)),
              ((nb068_alpha_dummy_135), (nb068_alpha_dummy_136 f)),
              ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
              ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
              ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
              ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
              ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
              ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
              ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
              ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
              ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
              ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
              ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
              ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
              ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
              ((nb068_alpha_dummy_001), x),
              ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))

@[expose]
noncomputable def nb068_split_alpha_0113 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_161), (nb068_alpha_dummy_162 f)),
        ((nb068_alpha_dummy_135), (nb068_alpha_dummy_136 f)),
        ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
        ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
        ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
        ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
        ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
        ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
        ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
        ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
        ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
        ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
        ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
        ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.classMem (Class.cv (nb068_alpha_dummy_161)) (Class.cab (nb068_alpha_dummy_131)
          (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_126))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_131))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_132))) (syn_csn (syn_c0c)))))))
      (Wff.classMem (Class.cv (nb068_alpha_dummy_162 f)) (Class.cab (nb068_alpha_dummy_133 f)
          (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_128 f))
            (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f))
              (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))
                (syn_csn (syn_c0c))))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cv (TAlphaVar.there
                (show (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_132) from (by
                    unfold nb068_alpha_dummy_132;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0154) 1))))
                (show (nb068_alpha_dummy_128 f) ≠ (nb068_alpha_dummy_134 f) from (by
                    unfold nb068_alpha_dummy_134;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0156 f) 1))))
                (TAlphaVar.there (show (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_131) from
                    (by
                      unfold nb068_alpha_dummy_131;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0154) 0))))
                  (show (nb068_alpha_dummy_128 f) ≠ (nb068_alpha_dummy_133 f) from (by
                      unfold nb068_alpha_dummy_133;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0156 f) 0))))
                  (TAlphaVar.there (show (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_161) from
                      (by
                        unfold nb068_alpha_dummy_161;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0158) 0))))
                    (show (nb068_alpha_dummy_128 f) ≠ (nb068_alpha_dummy_162 f) from (by
                        unfold nb068_alpha_dummy_162;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0159 f) 0)))) (TAlphaVar.there
                      (show (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_135) from (by
                          unfold nb068_alpha_dummy_135;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0155) 0))))
                      (show (nb068_alpha_dummy_128 f) ≠ (nb068_alpha_dummy_136 f) from (by
                          unfold nb068_alpha_dummy_136;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0157 f) 0))))
                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
              (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_125))).fv ∪
                    ((Class.cv (nb068_alpha_dummy_126))).fv) (by decide)) (freshVar_injective
                  (((Class.cv (nb068_alpha_dummy_127 f))).fv ∪
                    ((Class.cv (nb068_alpha_dummy_128 f))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb068_alpha_dummy_132) ≠
        (nb068_alpha_dummy_139) from (by
          unfold nb068_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 0)))) (show (nb068_alpha_dummy_134 f) ≠
        (nb068_alpha_dummy_141 f) from (by
          unfold nb068_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f) 0)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_132) ≠ (nb068_alpha_dummy_140) from (by
          unfold nb068_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 1)))) (show (nb068_alpha_dummy_134 f) ≠
        (nb068_alpha_dummy_142 f) from (by
          unfold nb068_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f) 1)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_132) ≠ (nb068_alpha_dummy_165) from (by
          unfold nb068_alpha_dummy_165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0162) 0)))) (show (nb068_alpha_dummy_134 f) ≠
        (nb068_alpha_dummy_166 f) from (by
          unfold nb068_alpha_dummy_166;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0163 f) 0)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_132) ≠ (nb068_alpha_dummy_163) from (by
          unfold nb068_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0160) 0)))) (show (nb068_alpha_dummy_134 f) ≠
        (nb068_alpha_dummy_164 f) from (by
          unfold nb068_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0161 f) 0)))) (TAlphaVar.here _ _ _)))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb068_alpha_dummy_132))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb068_alpha_dummy_134 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (nb068_split_alpha_0112 x y f)))))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb068_alpha_dummy_132) ≠
        (nb068_alpha_dummy_139) from (by
          unfold nb068_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 0)))) (show (nb068_alpha_dummy_134 f) ≠
        (nb068_alpha_dummy_141 f) from (by
          unfold nb068_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f) 0)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_132) ≠ (nb068_alpha_dummy_140) from (by
          unfold nb068_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 1)))) (show (nb068_alpha_dummy_134 f) ≠
        (nb068_alpha_dummy_142 f) from (by
          unfold nb068_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f) 1)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_132) ≠ (nb068_alpha_dummy_165) from (by
          unfold nb068_alpha_dummy_165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0162) 0)))) (show (nb068_alpha_dummy_134 f) ≠
        (nb068_alpha_dummy_166 f) from (by
          unfold nb068_alpha_dummy_166;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0163 f) 0)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_132) ≠ (nb068_alpha_dummy_163) from (by
          unfold nb068_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0160) 0)))) (show (nb068_alpha_dummy_134 f) ≠
        (nb068_alpha_dummy_164 f) from (by
          unfold nb068_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0161 f) 0)))) (TAlphaVar.here _ _ _)))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb068_alpha_dummy_132))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb068_alpha_dummy_134 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (nb068_split_alpha_0112 x y f)))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.refl_of_closed
                      [((nb068_alpha_dummy_163), (nb068_alpha_dummy_164 f)),
                        ((nb068_alpha_dummy_132), (nb068_alpha_dummy_134 f)),
                        ((nb068_alpha_dummy_131), (nb068_alpha_dummy_133 f)),
                        ((nb068_alpha_dummy_161), (nb068_alpha_dummy_162 f)),
                        ((nb068_alpha_dummy_135), (nb068_alpha_dummy_136 f)),
                        ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
                        ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
                        ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
                        ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
                        ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
                        ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
                        ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
                        ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
                        ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
                        ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
                        ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
                        ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
                        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                        ((nb068_alpha_dummy_001), x),
                        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                      (syn_ccompl (syn_csn (syn_c0c)))
                      (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))

@[expose]
noncomputable def nb068_split_alpha_0114 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_135), (nb068_alpha_dummy_136 f)),
        ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
        ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
        ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
        ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
        ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
        ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
        ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
        ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
        ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
        ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
        ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
        ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_135)) (syn_ccompl
            (Class.cab (nb068_alpha_dummy_131)
              (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_125))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_131))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_132)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb068_alpha_dummy_135)) (syn_ccompl
              (Class.cab (nb068_alpha_dummy_131)
                (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_126))
                  (Wff.classEq (Class.cv (nb068_alpha_dummy_131))
                    (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_132)))
                      (syn_csn (syn_c0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_136 f)) (syn_ccompl
            (Class.cab (nb068_alpha_dummy_133 f)
              (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_127 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb068_alpha_dummy_136 f)) (syn_ccompl
              (Class.cab (nb068_alpha_dummy_133 f)
                (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_128 f))
                  (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f))
                    (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))
                      (syn_csn (syn_c0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_132) from (by
                              unfold nb068_alpha_dummy_132;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0126) 1))))
                          (show (nb068_alpha_dummy_127 f) ≠ (nb068_alpha_dummy_134 f) from (by
                              unfold nb068_alpha_dummy_134;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0128 f) 1))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_131) from (by
                                unfold nb068_alpha_dummy_131;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0126) 0))))
                            (show (nb068_alpha_dummy_127 f) ≠ (nb068_alpha_dummy_133 f) from (by
                                unfold nb068_alpha_dummy_133;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0128 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_137) from (by
                                  unfold nb068_alpha_dummy_137;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0130) 0))))
                              (show (nb068_alpha_dummy_127 f) ≠ (nb068_alpha_dummy_138 f) from
                                (by
                                  unfold nb068_alpha_dummy_138;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0131 f) 0))))
                              (TAlphaVar.there
                                (show (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_135) from (by
                                    unfold nb068_alpha_dummy_135;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0127) 0)))) (show
                                  (nb068_alpha_dummy_127 f) ≠ (nb068_alpha_dummy_136 f) from (by
                                    unfold nb068_alpha_dummy_136;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0129 f)
                                            0)))) (TAlphaVar.there (freshVar_injective
                                    (((Class.cv (nb068_alpha_dummy_000))).fv) (by decide))
                                  (freshVar_injective (((Class.cv f)).fv) (by decide))
                                  (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb068_alpha_dummy_125))).fv ∪
                              ((Class.cv (nb068_alpha_dummy_126))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb068_alpha_dummy_127 f))).fv ∪
                              ((Class.cv (nb068_alpha_dummy_128 f))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb068_alpha_dummy_132) ≠ (nb068_alpha_dummy_139) from
                                    (by
                                      unfold nb068_alpha_dummy_139;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0132)
                                              0)))) (show
                                    (nb068_alpha_dummy_134 f) ≠ (nb068_alpha_dummy_141 f) from
                                    (by
                                      unfold nb068_alpha_dummy_141;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0133 f)
                                              0)))) (TAlphaVar.there (show
                                      (nb068_alpha_dummy_132) ≠ (nb068_alpha_dummy_140) from (by
                                        unfold nb068_alpha_dummy_140;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0132)
                                                1)))) (show (nb068_alpha_dummy_134 f) ≠
                                        (nb068_alpha_dummy_142 f) from (by
                                        unfold nb068_alpha_dummy_142;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0133 f)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb068_alpha_dummy_132))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb068_alpha_dummy_134 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _)))
                              (TAlphaClass.cab (nb068_split_alpha_0110 x y f)))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_132) from (by
                              unfold nb068_alpha_dummy_132;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0126) 1))))
                          (show (nb068_alpha_dummy_127 f) ≠ (nb068_alpha_dummy_134 f) from (by
                              unfold nb068_alpha_dummy_134;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0128 f) 1))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_131) from (by
                                unfold nb068_alpha_dummy_131;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0126) 0))))
                            (show (nb068_alpha_dummy_127 f) ≠ (nb068_alpha_dummy_133 f) from (by
                                unfold nb068_alpha_dummy_133;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0128 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_137) from (by
                                  unfold nb068_alpha_dummy_137;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0130) 0))))
                              (show (nb068_alpha_dummy_127 f) ≠ (nb068_alpha_dummy_138 f) from
                                (by
                                  unfold nb068_alpha_dummy_138;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0131 f) 0))))
                              (TAlphaVar.there
                                (show (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_135) from (by
                                    unfold nb068_alpha_dummy_135;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0127) 0)))) (show
                                  (nb068_alpha_dummy_127 f) ≠ (nb068_alpha_dummy_136 f) from (by
                                    unfold nb068_alpha_dummy_136;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0129 f)
                                            0)))) (TAlphaVar.there (freshVar_injective
                                    (((Class.cv (nb068_alpha_dummy_000))).fv) (by decide))
                                  (freshVar_injective (((Class.cv f)).fv) (by decide))
                                  (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb068_alpha_dummy_125))).fv ∪
                              ((Class.cv (nb068_alpha_dummy_126))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb068_alpha_dummy_127 f))).fv ∪
                              ((Class.cv (nb068_alpha_dummy_128 f))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb068_alpha_dummy_132) ≠ (nb068_alpha_dummy_139) from
                                    (by
                                      unfold nb068_alpha_dummy_139;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0132)
                                              0)))) (show
                                    (nb068_alpha_dummy_134 f) ≠ (nb068_alpha_dummy_141 f) from
                                    (by
                                      unfold nb068_alpha_dummy_141;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0133 f)
                                              0)))) (TAlphaVar.there (show
                                      (nb068_alpha_dummy_132) ≠ (nb068_alpha_dummy_140) from (by
                                        unfold nb068_alpha_dummy_140;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0132)
                                                1)))) (show (nb068_alpha_dummy_134 f) ≠
                                        (nb068_alpha_dummy_142 f) from (by
                                        unfold nb068_alpha_dummy_142;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0133 f)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb068_alpha_dummy_132))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb068_alpha_dummy_134 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                (nb068_split_alpha_0110 x y f))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj (nb068_split_alpha_0113 x y f)
              (nb068_split_alpha_0113 x y f)))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part045`. -/


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
noncomputable def nb068_split_alpha_0115 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_183), (nb068_alpha_dummy_186 f)),
        ((nb068_alpha_dummy_182), (nb068_alpha_dummy_185 f)),
        ((nb068_alpha_dummy_181), (nb068_alpha_dummy_184 f)),
        ((nb068_alpha_dummy_179), (nb068_alpha_dummy_180 f)),
        ((nb068_alpha_dummy_175), (nb068_alpha_dummy_177 f)),
        ((nb068_alpha_dummy_176), (nb068_alpha_dummy_178 f)),
        ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)),
        ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)),
        ((nb068_alpha_dummy_173), (nb068_alpha_dummy_174 f)),
        ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)),
        ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
        ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
        ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
        ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
        ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
        ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
        ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
        ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
        ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
        ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
        ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
        ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb068_alpha_dummy_182)) (Class.cv (nb068_alpha_dummy_183)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_181))
            (syn_cun (Class.cv (nb068_alpha_dummy_182)) (Class.cv (nb068_alpha_dummy_183))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_185 f))
            (Class.cv (nb068_alpha_dummy_186 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_184 f))
            (syn_cun (Class.cv (nb068_alpha_dummy_185 f))
              (Class.cv (nb068_alpha_dummy_186 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_182) ≠ (nb068_alpha_dummy_189) from (by
                              unfold nb068_alpha_dummy_189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0178) 0))))
                          (show (nb068_alpha_dummy_185 f) ≠ (nb068_alpha_dummy_190 f) from (by
                              unfold nb068_alpha_dummy_190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0179 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_182) ≠ (nb068_alpha_dummy_187) from (by
                                unfold nb068_alpha_dummy_187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0176) 0))))
                            (show (nb068_alpha_dummy_185 f) ≠ (nb068_alpha_dummy_188 f) from (by
                                unfold nb068_alpha_dummy_188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0177 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_183) ≠ (nb068_alpha_dummy_189) from (by
                              unfold nb068_alpha_dummy_189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0182) 0))))
                          (show (nb068_alpha_dummy_186 f) ≠ (nb068_alpha_dummy_190 f) from (by
                              unfold nb068_alpha_dummy_190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0183 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_183) ≠ (nb068_alpha_dummy_187) from (by
                                unfold nb068_alpha_dummy_187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0180) 0))))
                            (show (nb068_alpha_dummy_186 f) ≠ (nb068_alpha_dummy_188 f) from (by
                                unfold nb068_alpha_dummy_188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0181 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_182) ≠ (nb068_alpha_dummy_189) from (by
                              unfold nb068_alpha_dummy_189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0178) 0))))
                          (show (nb068_alpha_dummy_185 f) ≠ (nb068_alpha_dummy_190 f) from (by
                              unfold nb068_alpha_dummy_190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0179 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_182) ≠ (nb068_alpha_dummy_187) from (by
                                unfold nb068_alpha_dummy_187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0176) 0))))
                            (show (nb068_alpha_dummy_185 f) ≠ (nb068_alpha_dummy_188 f) from (by
                                unfold nb068_alpha_dummy_188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0177 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_183) ≠ (nb068_alpha_dummy_189) from (by
                              unfold nb068_alpha_dummy_189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0182) 0))))
                          (show (nb068_alpha_dummy_186 f) ≠ (nb068_alpha_dummy_190 f) from (by
                              unfold nb068_alpha_dummy_190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0183 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_183) ≠ (nb068_alpha_dummy_187) from (by
                                unfold nb068_alpha_dummy_187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0180) 0))))
                            (show (nb068_alpha_dummy_186 f) ≠ (nb068_alpha_dummy_188 f) from (by
                                unfold nb068_alpha_dummy_188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0181 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb068_alpha_dummy_183), (nb068_alpha_dummy_186 f)),
          ((nb068_alpha_dummy_182), (nb068_alpha_dummy_185 f)),
          ((nb068_alpha_dummy_181), (nb068_alpha_dummy_184 f)),
          ((nb068_alpha_dummy_179), (nb068_alpha_dummy_180 f)),
          ((nb068_alpha_dummy_175), (nb068_alpha_dummy_177 f)),
          ((nb068_alpha_dummy_176), (nb068_alpha_dummy_178 f)),
          ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)),
          ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)),
          ((nb068_alpha_dummy_173), (nb068_alpha_dummy_174 f)),
          ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)),
          ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
          ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
          ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
          ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
          ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
          ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
          ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
          ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
          ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
          ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
          ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
          ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
          ((nb068_alpha_dummy_001), x),
          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_182) ≠ (nb068_alpha_dummy_193) from (by
                                unfold nb068_alpha_dummy_193;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0186) 0))))
                            (show (nb068_alpha_dummy_185 f) ≠ (nb068_alpha_dummy_194 f) from (by
                                unfold nb068_alpha_dummy_194;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0187 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_182) ≠ (nb068_alpha_dummy_191) from (by
                                  unfold nb068_alpha_dummy_191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0184) 0))))
                              (show (nb068_alpha_dummy_185 f) ≠ (nb068_alpha_dummy_192 f) from
                                (by
                                  unfold nb068_alpha_dummy_192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0185 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_182) ≠ (nb068_alpha_dummy_193) from (by
                                unfold nb068_alpha_dummy_193;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0186) 0))))
                            (show (nb068_alpha_dummy_185 f) ≠ (nb068_alpha_dummy_194 f) from (by
                                unfold nb068_alpha_dummy_194;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0187 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_182) ≠ (nb068_alpha_dummy_191) from (by
                                  unfold nb068_alpha_dummy_191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0184) 0))))
                              (show (nb068_alpha_dummy_185 f) ≠ (nb068_alpha_dummy_192 f) from
                                (by
                                  unfold nb068_alpha_dummy_192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0185 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_183) ≠ (nb068_alpha_dummy_195) from (by
                                unfold nb068_alpha_dummy_195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0190) 0))))
                            (show (nb068_alpha_dummy_186 f) ≠ (nb068_alpha_dummy_196 f) from (by
                                unfold nb068_alpha_dummy_196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0191 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_183) ≠ (nb068_alpha_dummy_191) from (by
                                  unfold nb068_alpha_dummy_191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0188) 0))))
                              (show (nb068_alpha_dummy_186 f) ≠ (nb068_alpha_dummy_192 f) from
                                (by
                                  unfold nb068_alpha_dummy_192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0189 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_183) ≠ (nb068_alpha_dummy_195) from (by
                                unfold nb068_alpha_dummy_195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0190) 0))))
                            (show (nb068_alpha_dummy_186 f) ≠ (nb068_alpha_dummy_196 f) from (by
                                unfold nb068_alpha_dummy_196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0191 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_183) ≠ (nb068_alpha_dummy_191) from (by
                                  unfold nb068_alpha_dummy_191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0188) 0))))
                              (show (nb068_alpha_dummy_186 f) ≠ (nb068_alpha_dummy_192 f) from
                                (by
                                  unfold nb068_alpha_dummy_192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0189 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb068_split_alpha_0116 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_179), (nb068_alpha_dummy_180 f)),
        ((nb068_alpha_dummy_175), (nb068_alpha_dummy_177 f)),
        ((nb068_alpha_dummy_176), (nb068_alpha_dummy_178 f)),
        ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)),
        ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)),
        ((nb068_alpha_dummy_173), (nb068_alpha_dummy_174 f)),
        ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)),
        ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
        ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
        ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
        ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
        ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
        ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
        ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
        ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
        ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
        ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
        ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
        ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb068_alpha_dummy_179))
              (syn_cplc (Class.cv (nb068_alpha_dummy_175)) (syn_c1c)))
            (Wff.classMem (Class.cv (nb068_alpha_dummy_175)) (syn_cnnc)))) (syn_wa
          (Wff.classMem (Class.cv (nb068_alpha_dummy_179)) (Class.cv (nb068_alpha_dummy_175)))
          (Wff.neg (Wff.classMem (Class.cv (nb068_alpha_dummy_175)) (syn_cnnc)))))
      (Wff.imp (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb068_alpha_dummy_180 f))
              (syn_cplc (Class.cv (nb068_alpha_dummy_177 f)) (syn_c1c)))
            (Wff.classMem (Class.cv (nb068_alpha_dummy_177 f)) (syn_cnnc)))) (syn_wa
          (Wff.classMem (Class.cv (nb068_alpha_dummy_180 f))
            (Class.cv (nb068_alpha_dummy_177 f)))
          (Wff.neg (Wff.classMem (Class.cv (nb068_alpha_dummy_177 f)) (syn_cnnc))))) :=
  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068_alpha_dummy_175) ≠ (nb068_alpha_dummy_182) from (by
                          unfold nb068_alpha_dummy_182;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0174) 1))))
                      (show (nb068_alpha_dummy_177 f) ≠ (nb068_alpha_dummy_185 f) from (by
                          unfold nb068_alpha_dummy_185;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0175 f) 1))))
                      (TAlphaVar.there
                        (show (nb068_alpha_dummy_175) ≠ (nb068_alpha_dummy_181) from (by
                            unfold nb068_alpha_dummy_181;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0174) 0))))
                        (show (nb068_alpha_dummy_177 f) ≠ (nb068_alpha_dummy_184 f) from (by
                            unfold nb068_alpha_dummy_184;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0175 f) 0))))
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_175) ≠ (nb068_alpha_dummy_179) from (by
                              unfold nb068_alpha_dummy_179;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0172) 0))))
                          (show (nb068_alpha_dummy_177 f) ≠ (nb068_alpha_dummy_180 f) from (by
                              unfold nb068_alpha_dummy_180;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
                          (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb068_alpha_dummy_183), (nb068_alpha_dummy_186 f)),
                          ((nb068_alpha_dummy_182), (nb068_alpha_dummy_185 f)),
                          ((nb068_alpha_dummy_181), (nb068_alpha_dummy_184 f)),
                          ((nb068_alpha_dummy_179), (nb068_alpha_dummy_180 f)),
                          ((nb068_alpha_dummy_175), (nb068_alpha_dummy_177 f)),
                          ((nb068_alpha_dummy_176), (nb068_alpha_dummy_178 f)),
                          ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)),
                          ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)),
                          ((nb068_alpha_dummy_173), (nb068_alpha_dummy_174 f)),
                          ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)),
                          ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
                          ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
                          ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
                          ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
                          ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
                          ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
                          ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
                          ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
                          ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
                          ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
                          ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
                          ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
                          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                          ((nb068_alpha_dummy_001), x),
                          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                        (syn_c1c) (by simp only [fv_syn_c1c])))
                    (TAlphaWff.neg (nb068_split_alpha_0115 x y f)))))))) (TAlphaWff.classMem
          (TAlphaClass.cv (TAlphaVar.there
              (show (nb068_alpha_dummy_175) ≠ (nb068_alpha_dummy_179) from (by
                  unfold nb068_alpha_dummy_179;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0172) 0))))
              (show (nb068_alpha_dummy_177 f) ≠ (nb068_alpha_dummy_180 f) from (by
                  unfold nb068_alpha_dummy_180;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
            [((nb068_alpha_dummy_179), (nb068_alpha_dummy_180 f)),
              ((nb068_alpha_dummy_175), (nb068_alpha_dummy_177 f)),
              ((nb068_alpha_dummy_176), (nb068_alpha_dummy_178 f)),
              ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)),
              ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)),
              ((nb068_alpha_dummy_173), (nb068_alpha_dummy_174 f)),
              ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)),
              ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
              ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
              ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
              ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
              ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
              ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
              ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
              ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
              ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
              ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
              ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
              ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
              ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
              ((nb068_alpha_dummy_001), x),
              ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
          (TAlphaVar.there (show (nb068_alpha_dummy_175) ≠ (nb068_alpha_dummy_179) from (by
                unfold nb068_alpha_dummy_179;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0172) 0))))
            (show (nb068_alpha_dummy_177 f) ≠ (nb068_alpha_dummy_180 f) from (by
                unfold nb068_alpha_dummy_180;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
            (TAlphaVar.there (show (nb068_alpha_dummy_175) ≠ (nb068_alpha_dummy_179) from (by
                  unfold nb068_alpha_dummy_179;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0172) 0))))
              (show (nb068_alpha_dummy_177 f) ≠ (nb068_alpha_dummy_180 f) from (by
                  unfold nb068_alpha_dummy_180;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
            [((nb068_alpha_dummy_179), (nb068_alpha_dummy_180 f)),
              ((nb068_alpha_dummy_175), (nb068_alpha_dummy_177 f)),
              ((nb068_alpha_dummy_176), (nb068_alpha_dummy_178 f)),
              ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)),
              ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)),
              ((nb068_alpha_dummy_173), (nb068_alpha_dummy_174 f)),
              ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)),
              ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
              ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
              ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
              ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
              ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
              ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
              ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
              ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
              ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
              ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
              ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
              ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
              ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
              ((nb068_alpha_dummy_001), x),
              ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))

@[expose]
noncomputable def nb068_split_alpha_0117 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_183), (nb068_alpha_dummy_186 f)),
        ((nb068_alpha_dummy_182), (nb068_alpha_dummy_185 f)),
        ((nb068_alpha_dummy_181), (nb068_alpha_dummy_184 f)),
        ((nb068_alpha_dummy_179), (nb068_alpha_dummy_180 f)),
        ((nb068_alpha_dummy_175), (nb068_alpha_dummy_177 f)),
        ((nb068_alpha_dummy_176), (nb068_alpha_dummy_178 f)),
        ((nb068_alpha_dummy_201), (nb068_alpha_dummy_202 f)),
        ((nb068_alpha_dummy_199), (nb068_alpha_dummy_200 f)),
        ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)),
        ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)),
        ((nb068_alpha_dummy_197), (nb068_alpha_dummy_198 f)),
        ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)),
        ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
        ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
        ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
        ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
        ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
        ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
        ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
        ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
        ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
        ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
        ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
        ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb068_alpha_dummy_182)) (Class.cv (nb068_alpha_dummy_183)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_181))
            (syn_cun (Class.cv (nb068_alpha_dummy_182)) (Class.cv (nb068_alpha_dummy_183))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_185 f))
            (Class.cv (nb068_alpha_dummy_186 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_184 f))
            (syn_cun (Class.cv (nb068_alpha_dummy_185 f))
              (Class.cv (nb068_alpha_dummy_186 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_182) ≠ (nb068_alpha_dummy_189) from (by
                              unfold nb068_alpha_dummy_189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0178) 0))))
                          (show (nb068_alpha_dummy_185 f) ≠ (nb068_alpha_dummy_190 f) from (by
                              unfold nb068_alpha_dummy_190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0179 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_182) ≠ (nb068_alpha_dummy_187) from (by
                                unfold nb068_alpha_dummy_187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0176) 0))))
                            (show (nb068_alpha_dummy_185 f) ≠ (nb068_alpha_dummy_188 f) from (by
                                unfold nb068_alpha_dummy_188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0177 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_183) ≠ (nb068_alpha_dummy_189) from (by
                              unfold nb068_alpha_dummy_189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0182) 0))))
                          (show (nb068_alpha_dummy_186 f) ≠ (nb068_alpha_dummy_190 f) from (by
                              unfold nb068_alpha_dummy_190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0183 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_183) ≠ (nb068_alpha_dummy_187) from (by
                                unfold nb068_alpha_dummy_187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0180) 0))))
                            (show (nb068_alpha_dummy_186 f) ≠ (nb068_alpha_dummy_188 f) from (by
                                unfold nb068_alpha_dummy_188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0181 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_182) ≠ (nb068_alpha_dummy_189) from (by
                              unfold nb068_alpha_dummy_189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0178) 0))))
                          (show (nb068_alpha_dummy_185 f) ≠ (nb068_alpha_dummy_190 f) from (by
                              unfold nb068_alpha_dummy_190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0179 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_182) ≠ (nb068_alpha_dummy_187) from (by
                                unfold nb068_alpha_dummy_187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0176) 0))))
                            (show (nb068_alpha_dummy_185 f) ≠ (nb068_alpha_dummy_188 f) from (by
                                unfold nb068_alpha_dummy_188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0177 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_183) ≠ (nb068_alpha_dummy_189) from (by
                              unfold nb068_alpha_dummy_189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0182) 0))))
                          (show (nb068_alpha_dummy_186 f) ≠ (nb068_alpha_dummy_190 f) from (by
                              unfold nb068_alpha_dummy_190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0183 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_183) ≠ (nb068_alpha_dummy_187) from (by
                                unfold nb068_alpha_dummy_187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0180) 0))))
                            (show (nb068_alpha_dummy_186 f) ≠ (nb068_alpha_dummy_188 f) from (by
                                unfold nb068_alpha_dummy_188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0181 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb068_alpha_dummy_183), (nb068_alpha_dummy_186 f)),
          ((nb068_alpha_dummy_182), (nb068_alpha_dummy_185 f)),
          ((nb068_alpha_dummy_181), (nb068_alpha_dummy_184 f)),
          ((nb068_alpha_dummy_179), (nb068_alpha_dummy_180 f)),
          ((nb068_alpha_dummy_175), (nb068_alpha_dummy_177 f)),
          ((nb068_alpha_dummy_176), (nb068_alpha_dummy_178 f)),
          ((nb068_alpha_dummy_201), (nb068_alpha_dummy_202 f)),
          ((nb068_alpha_dummy_199), (nb068_alpha_dummy_200 f)),
          ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)),
          ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)),
          ((nb068_alpha_dummy_197), (nb068_alpha_dummy_198 f)),
          ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)),
          ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
          ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
          ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
          ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
          ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
          ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
          ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
          ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
          ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
          ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
          ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
          ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
          ((nb068_alpha_dummy_001), x),
          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_182) ≠ (nb068_alpha_dummy_193) from (by
                                unfold nb068_alpha_dummy_193;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0186) 0))))
                            (show (nb068_alpha_dummy_185 f) ≠ (nb068_alpha_dummy_194 f) from (by
                                unfold nb068_alpha_dummy_194;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0187 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_182) ≠ (nb068_alpha_dummy_191) from (by
                                  unfold nb068_alpha_dummy_191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0184) 0))))
                              (show (nb068_alpha_dummy_185 f) ≠ (nb068_alpha_dummy_192 f) from
                                (by
                                  unfold nb068_alpha_dummy_192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0185 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_182) ≠ (nb068_alpha_dummy_193) from (by
                                unfold nb068_alpha_dummy_193;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0186) 0))))
                            (show (nb068_alpha_dummy_185 f) ≠ (nb068_alpha_dummy_194 f) from (by
                                unfold nb068_alpha_dummy_194;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0187 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_182) ≠ (nb068_alpha_dummy_191) from (by
                                  unfold nb068_alpha_dummy_191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0184) 0))))
                              (show (nb068_alpha_dummy_185 f) ≠ (nb068_alpha_dummy_192 f) from
                                (by
                                  unfold nb068_alpha_dummy_192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0185 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_183) ≠ (nb068_alpha_dummy_195) from (by
                                unfold nb068_alpha_dummy_195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0190) 0))))
                            (show (nb068_alpha_dummy_186 f) ≠ (nb068_alpha_dummy_196 f) from (by
                                unfold nb068_alpha_dummy_196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0191 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_183) ≠ (nb068_alpha_dummy_191) from (by
                                  unfold nb068_alpha_dummy_191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0188) 0))))
                              (show (nb068_alpha_dummy_186 f) ≠ (nb068_alpha_dummy_192 f) from
                                (by
                                  unfold nb068_alpha_dummy_192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0189 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_183) ≠ (nb068_alpha_dummy_195) from (by
                                unfold nb068_alpha_dummy_195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0190) 0))))
                            (show (nb068_alpha_dummy_186 f) ≠ (nb068_alpha_dummy_196 f) from (by
                                unfold nb068_alpha_dummy_196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0191 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_183) ≠ (nb068_alpha_dummy_191) from (by
                                  unfold nb068_alpha_dummy_191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0188) 0))))
                              (show (nb068_alpha_dummy_186 f) ≠ (nb068_alpha_dummy_192 f) from
                                (by
                                  unfold nb068_alpha_dummy_192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0189 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb068_split_alpha_0118 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_179), (nb068_alpha_dummy_180 f)),
        ((nb068_alpha_dummy_175), (nb068_alpha_dummy_177 f)),
        ((nb068_alpha_dummy_176), (nb068_alpha_dummy_178 f)),
        ((nb068_alpha_dummy_201), (nb068_alpha_dummy_202 f)),
        ((nb068_alpha_dummy_199), (nb068_alpha_dummy_200 f)),
        ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)),
        ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)),
        ((nb068_alpha_dummy_197), (nb068_alpha_dummy_198 f)),
        ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)),
        ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
        ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
        ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
        ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
        ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
        ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
        ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
        ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
        ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
        ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
        ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
        ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb068_alpha_dummy_179))
              (syn_cplc (Class.cv (nb068_alpha_dummy_175)) (syn_c1c)))
            (Wff.classMem (Class.cv (nb068_alpha_dummy_175)) (syn_cnnc)))) (syn_wa
          (Wff.classMem (Class.cv (nb068_alpha_dummy_179)) (Class.cv (nb068_alpha_dummy_175)))
          (Wff.neg (Wff.classMem (Class.cv (nb068_alpha_dummy_175)) (syn_cnnc)))))
      (Wff.imp (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb068_alpha_dummy_180 f))
              (syn_cplc (Class.cv (nb068_alpha_dummy_177 f)) (syn_c1c)))
            (Wff.classMem (Class.cv (nb068_alpha_dummy_177 f)) (syn_cnnc)))) (syn_wa
          (Wff.classMem (Class.cv (nb068_alpha_dummy_180 f))
            (Class.cv (nb068_alpha_dummy_177 f)))
          (Wff.neg (Wff.classMem (Class.cv (nb068_alpha_dummy_177 f)) (syn_cnnc))))) :=
  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068_alpha_dummy_175) ≠ (nb068_alpha_dummy_182) from (by
                          unfold nb068_alpha_dummy_182;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0174) 1))))
                      (show (nb068_alpha_dummy_177 f) ≠ (nb068_alpha_dummy_185 f) from (by
                          unfold nb068_alpha_dummy_185;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0175 f) 1))))
                      (TAlphaVar.there
                        (show (nb068_alpha_dummy_175) ≠ (nb068_alpha_dummy_181) from (by
                            unfold nb068_alpha_dummy_181;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0174) 0))))
                        (show (nb068_alpha_dummy_177 f) ≠ (nb068_alpha_dummy_184 f) from (by
                            unfold nb068_alpha_dummy_184;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0175 f) 0))))
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_175) ≠ (nb068_alpha_dummy_179) from (by
                              unfold nb068_alpha_dummy_179;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0172) 0))))
                          (show (nb068_alpha_dummy_177 f) ≠ (nb068_alpha_dummy_180 f) from (by
                              unfold nb068_alpha_dummy_180;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
                          (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb068_alpha_dummy_183), (nb068_alpha_dummy_186 f)),
                          ((nb068_alpha_dummy_182), (nb068_alpha_dummy_185 f)),
                          ((nb068_alpha_dummy_181), (nb068_alpha_dummy_184 f)),
                          ((nb068_alpha_dummy_179), (nb068_alpha_dummy_180 f)),
                          ((nb068_alpha_dummy_175), (nb068_alpha_dummy_177 f)),
                          ((nb068_alpha_dummy_176), (nb068_alpha_dummy_178 f)),
                          ((nb068_alpha_dummy_201), (nb068_alpha_dummy_202 f)),
                          ((nb068_alpha_dummy_199), (nb068_alpha_dummy_200 f)),
                          ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)),
                          ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)),
                          ((nb068_alpha_dummy_197), (nb068_alpha_dummy_198 f)),
                          ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)),
                          ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
                          ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
                          ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
                          ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
                          ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
                          ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
                          ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
                          ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
                          ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
                          ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
                          ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
                          ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
                          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                          ((nb068_alpha_dummy_001), x),
                          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                        (syn_c1c) (by simp only [fv_syn_c1c])))
                    (TAlphaWff.neg (nb068_split_alpha_0117 x y f)))))))) (TAlphaWff.classMem
          (TAlphaClass.cv (TAlphaVar.there
              (show (nb068_alpha_dummy_175) ≠ (nb068_alpha_dummy_179) from (by
                  unfold nb068_alpha_dummy_179;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0172) 0))))
              (show (nb068_alpha_dummy_177 f) ≠ (nb068_alpha_dummy_180 f) from (by
                  unfold nb068_alpha_dummy_180;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
            [((nb068_alpha_dummy_179), (nb068_alpha_dummy_180 f)),
              ((nb068_alpha_dummy_175), (nb068_alpha_dummy_177 f)),
              ((nb068_alpha_dummy_176), (nb068_alpha_dummy_178 f)),
              ((nb068_alpha_dummy_201), (nb068_alpha_dummy_202 f)),
              ((nb068_alpha_dummy_199), (nb068_alpha_dummy_200 f)),
              ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)),
              ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)),
              ((nb068_alpha_dummy_197), (nb068_alpha_dummy_198 f)),
              ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)),
              ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
              ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
              ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
              ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
              ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
              ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
              ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
              ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
              ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
              ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
              ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
              ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
              ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
              ((nb068_alpha_dummy_001), x),
              ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
          (TAlphaVar.there (show (nb068_alpha_dummy_175) ≠ (nb068_alpha_dummy_179) from (by
                unfold nb068_alpha_dummy_179;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0172) 0))))
            (show (nb068_alpha_dummy_177 f) ≠ (nb068_alpha_dummy_180 f) from (by
                unfold nb068_alpha_dummy_180;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
            (TAlphaVar.there (show (nb068_alpha_dummy_175) ≠ (nb068_alpha_dummy_179) from (by
                  unfold nb068_alpha_dummy_179;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0172) 0))))
              (show (nb068_alpha_dummy_177 f) ≠ (nb068_alpha_dummy_180 f) from (by
                  unfold nb068_alpha_dummy_180;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
            [((nb068_alpha_dummy_179), (nb068_alpha_dummy_180 f)),
              ((nb068_alpha_dummy_175), (nb068_alpha_dummy_177 f)),
              ((nb068_alpha_dummy_176), (nb068_alpha_dummy_178 f)),
              ((nb068_alpha_dummy_201), (nb068_alpha_dummy_202 f)),
              ((nb068_alpha_dummy_199), (nb068_alpha_dummy_200 f)),
              ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)),
              ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)),
              ((nb068_alpha_dummy_197), (nb068_alpha_dummy_198 f)),
              ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)),
              ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
              ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
              ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
              ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
              ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
              ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
              ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
              ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
              ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
              ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
              ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
              ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
              ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
              ((nb068_alpha_dummy_001), x),
              ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part046`. -/


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
noncomputable def nb068_split_alpha_0119 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)),
        ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)),
        ((nb068_alpha_dummy_197), (nb068_alpha_dummy_198 f)),
        ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)),
        ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
        ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
        ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
        ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
        ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
        ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
        ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
        ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
        ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
        ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
        ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
        ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_168))
          (Class.cv (nb068_alpha_dummy_125))) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_167))
            (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_168))) (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_170 f))
          (Class.cv (nb068_alpha_dummy_127 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f))
            (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_170 f))) (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_168) from (by
              unfold nb068_alpha_dummy_168;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0192) 1))))
          (show (nb068_alpha_dummy_127 f) ≠ (nb068_alpha_dummy_170 f) from (by
              unfold nb068_alpha_dummy_170;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0194 f) 1))))
          (TAlphaVar.there (show (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_167) from (by
                unfold nb068_alpha_dummy_167;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0192) 0))))
            (show (nb068_alpha_dummy_127 f) ≠ (nb068_alpha_dummy_169 f) from (by
                unfold nb068_alpha_dummy_169;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0194 f) 0))))
            (TAlphaVar.there (show (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_197) from (by
                  unfold nb068_alpha_dummy_197;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0196) 0))))
              (show (nb068_alpha_dummy_127 f) ≠ (nb068_alpha_dummy_198 f) from (by
                  unfold nb068_alpha_dummy_198;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0197 f) 0))))
              (TAlphaVar.there (show (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_171) from (by
                    unfold nb068_alpha_dummy_171;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0193) 0))))
                (show (nb068_alpha_dummy_127 f) ≠ (nb068_alpha_dummy_172 f) from (by
                    unfold nb068_alpha_dummy_172;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0195 f) 0))))
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_000))).fv)
                    (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
                  (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb068_alpha_dummy_126))).fv ∪
                ((Class.cv (nb068_alpha_dummy_125))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb068_alpha_dummy_128 f))).fv ∪
                ((Class.cv (nb068_alpha_dummy_127 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb068_alpha_dummy_168) ≠ (nb068_alpha_dummy_175) from (by
                                        unfold nb068_alpha_dummy_175;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0170)
                                                0)))) (show (nb068_alpha_dummy_170 f) ≠
                                        (nb068_alpha_dummy_177 f) from (by
                                        unfold nb068_alpha_dummy_177;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0171 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068_alpha_dummy_168) ≠ (nb068_alpha_dummy_176) from
                                        (by
                                          unfold nb068_alpha_dummy_176;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0170)
                                                  1)))) (show (nb068_alpha_dummy_170 f) ≠
        (nb068_alpha_dummy_178 f) from (by
                                          unfold nb068_alpha_dummy_178;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0171 f) 1))))
                                      (TAlphaVar.there (show (nb068_alpha_dummy_168) ≠
        (nb068_alpha_dummy_201) from (by
          unfold nb068_alpha_dummy_201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0200) 0)))) (show (nb068_alpha_dummy_170 f) ≠
        (nb068_alpha_dummy_202 f) from (by
          unfold nb068_alpha_dummy_202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0201 f) 0)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_168) ≠ (nb068_alpha_dummy_199) from (by
          unfold nb068_alpha_dummy_199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0198) 0)))) (show (nb068_alpha_dummy_170 f) ≠
        (nb068_alpha_dummy_200 f) from (by
          unfold nb068_alpha_dummy_200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0199 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb068_alpha_dummy_168))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb068_alpha_dummy_170 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _)))
                                (TAlphaClass.cab (nb068_split_alpha_0118 x y f)))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb068_alpha_dummy_168) ≠ (nb068_alpha_dummy_175) from (by
                                        unfold nb068_alpha_dummy_175;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0170)
                                                0)))) (show (nb068_alpha_dummy_170 f) ≠
                                        (nb068_alpha_dummy_177 f) from (by
                                        unfold nb068_alpha_dummy_177;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0171 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068_alpha_dummy_168) ≠ (nb068_alpha_dummy_176) from
                                        (by
                                          unfold nb068_alpha_dummy_176;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0170)
                                                  1)))) (show (nb068_alpha_dummy_170 f) ≠
        (nb068_alpha_dummy_178 f) from (by
                                          unfold nb068_alpha_dummy_178;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0171 f) 1))))
                                      (TAlphaVar.there (show (nb068_alpha_dummy_168) ≠
        (nb068_alpha_dummy_201) from (by
          unfold nb068_alpha_dummy_201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0200) 0)))) (show (nb068_alpha_dummy_170 f) ≠
        (nb068_alpha_dummy_202 f) from (by
          unfold nb068_alpha_dummy_202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0201 f) 0)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_168) ≠ (nb068_alpha_dummy_199) from (by
          unfold nb068_alpha_dummy_199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0198) 0)))) (show (nb068_alpha_dummy_170 f) ≠
        (nb068_alpha_dummy_200 f) from (by
          unfold nb068_alpha_dummy_200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0199 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb068_alpha_dummy_168))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb068_alpha_dummy_170 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _)))
                                (TAlphaClass.cab (nb068_split_alpha_0118 x y f)))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb068_alpha_dummy_199), (nb068_alpha_dummy_200 f)),
                    ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)),
                    ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)),
                    ((nb068_alpha_dummy_197), (nb068_alpha_dummy_198 f)),
                    ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)),
                    ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
                    ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
                    ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
                    ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
                    ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
                    ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
                    ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
                    ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
                    ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
                    ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
                    ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
                    ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
                    ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                    ((nb068_alpha_dummy_001), x),
                    ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                  (syn_ccompl (syn_csn (syn_c0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

@[expose]
noncomputable def nb068_split_alpha_0120 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)),
        ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
        ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
        ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
        ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
        ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
        ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
        ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
        ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
        ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
        ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
        ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
        ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_171)) (syn_ccompl
            (Class.cab (nb068_alpha_dummy_167)
              (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_126))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_167))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_168)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb068_alpha_dummy_171)) (syn_ccompl
              (Class.cab (nb068_alpha_dummy_167)
                (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_125))
                  (Wff.classEq (Class.cv (nb068_alpha_dummy_167))
                    (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_168)))
                      (syn_csn (syn_c0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_172 f)) (syn_ccompl
            (Class.cab (nb068_alpha_dummy_169 f)
              (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_128 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f))
                  (syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb068_alpha_dummy_172 f)) (syn_ccompl
              (Class.cab (nb068_alpha_dummy_169 f)
                (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_127 f))
                  (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f))
                    (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))
                      (syn_csn (syn_c0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_168) from (by
                              unfold nb068_alpha_dummy_168;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0164) 1))))
                          (show (nb068_alpha_dummy_128 f) ≠ (nb068_alpha_dummy_170 f) from (by
                              unfold nb068_alpha_dummy_170;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0166 f) 1))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_167) from (by
                                unfold nb068_alpha_dummy_167;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0164) 0))))
                            (show (nb068_alpha_dummy_128 f) ≠ (nb068_alpha_dummy_169 f) from (by
                                unfold nb068_alpha_dummy_169;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0166 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_173) from (by
                                  unfold nb068_alpha_dummy_173;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0168) 0))))
                              (show (nb068_alpha_dummy_128 f) ≠ (nb068_alpha_dummy_174 f) from
                                (by
                                  unfold nb068_alpha_dummy_174;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0169 f) 0))))
                              (TAlphaVar.there
                                (show (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_171) from (by
                                    unfold nb068_alpha_dummy_171;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0165) 0)))) (show
                                  (nb068_alpha_dummy_128 f) ≠ (nb068_alpha_dummy_172 f) from (by
                                    unfold nb068_alpha_dummy_172;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0167 f)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb068_alpha_dummy_126))).fv ∪
                              ((Class.cv (nb068_alpha_dummy_125))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb068_alpha_dummy_128 f))).fv ∪
                              ((Class.cv (nb068_alpha_dummy_127 f))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb068_alpha_dummy_168) ≠ (nb068_alpha_dummy_175) from
                                    (by
                                      unfold nb068_alpha_dummy_175;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0170)
                                              0)))) (show
                                    (nb068_alpha_dummy_170 f) ≠ (nb068_alpha_dummy_177 f) from
                                    (by
                                      unfold nb068_alpha_dummy_177;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0171 f)
                                              0)))) (TAlphaVar.there (show
                                      (nb068_alpha_dummy_168) ≠ (nb068_alpha_dummy_176) from (by
                                        unfold nb068_alpha_dummy_176;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0170)
                                                1)))) (show (nb068_alpha_dummy_170 f) ≠
                                        (nb068_alpha_dummy_178 f) from (by
                                        unfold nb068_alpha_dummy_178;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0171 f)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb068_alpha_dummy_168))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb068_alpha_dummy_170 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _)))
                              (TAlphaClass.cab (nb068_split_alpha_0116 x y f)))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_168) from (by
                              unfold nb068_alpha_dummy_168;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0164) 1))))
                          (show (nb068_alpha_dummy_128 f) ≠ (nb068_alpha_dummy_170 f) from (by
                              unfold nb068_alpha_dummy_170;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0166 f) 1))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_167) from (by
                                unfold nb068_alpha_dummy_167;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0164) 0))))
                            (show (nb068_alpha_dummy_128 f) ≠ (nb068_alpha_dummy_169 f) from (by
                                unfold nb068_alpha_dummy_169;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0166 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_173) from (by
                                  unfold nb068_alpha_dummy_173;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0168) 0))))
                              (show (nb068_alpha_dummy_128 f) ≠ (nb068_alpha_dummy_174 f) from
                                (by
                                  unfold nb068_alpha_dummy_174;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0169 f) 0))))
                              (TAlphaVar.there
                                (show (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_171) from (by
                                    unfold nb068_alpha_dummy_171;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0165) 0)))) (show
                                  (nb068_alpha_dummy_128 f) ≠ (nb068_alpha_dummy_172 f) from (by
                                    unfold nb068_alpha_dummy_172;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0167 f)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb068_alpha_dummy_126))).fv ∪
                              ((Class.cv (nb068_alpha_dummy_125))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb068_alpha_dummy_128 f))).fv ∪
                              ((Class.cv (nb068_alpha_dummy_127 f))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb068_alpha_dummy_168) ≠ (nb068_alpha_dummy_175) from
                                    (by
                                      unfold nb068_alpha_dummy_175;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0170)
                                              0)))) (show
                                    (nb068_alpha_dummy_170 f) ≠ (nb068_alpha_dummy_177 f) from
                                    (by
                                      unfold nb068_alpha_dummy_177;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0171 f)
                                              0)))) (TAlphaVar.there (show
                                      (nb068_alpha_dummy_168) ≠ (nb068_alpha_dummy_176) from (by
                                        unfold nb068_alpha_dummy_176;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0170)
                                                1)))) (show (nb068_alpha_dummy_170 f) ≠
                                        (nb068_alpha_dummy_178 f) from (by
                                        unfold nb068_alpha_dummy_178;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0171 f)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb068_alpha_dummy_168))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb068_alpha_dummy_170 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                (nb068_split_alpha_0116 x y f))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb068_split_alpha_0119 x y f)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb068_split_alpha_0119 x y f)))))))))))

@[expose]
noncomputable def nb068_split_alpha_0121 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
        ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
        ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
        ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
        ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
        ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
        ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
        ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
        ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.classMem
        (syn_cop (Class.cv (nb068_alpha_dummy_408)) (Class.cv (nb068_alpha_dummy_407)))
        (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))
      (Wff.classMem (syn_cop (Class.cv (nb068_alpha_dummy_410 f))
          (Class.cv (nb068_alpha_dummy_409 f))) (syn_ccnv (Class.cv f))) :=
  (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb068_alpha_dummy_408) ≠ (nb068_alpha_dummy_450) from (by
                                    unfold nb068_alpha_dummy_450;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0462) 1)))) (show
                                  (nb068_alpha_dummy_410 f) ≠ (nb068_alpha_dummy_452 f) from (by
                                    unfold nb068_alpha_dummy_452;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0464 f)
                                            1)))) (TAlphaVar.there
                                  (show (nb068_alpha_dummy_408) ≠ (nb068_alpha_dummy_449) from
                                    (by
                                      unfold nb068_alpha_dummy_449;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0462)
                                              0)))) (show
                                    (nb068_alpha_dummy_410 f) ≠ (nb068_alpha_dummy_451 f) from
                                    (by
                                      unfold nb068_alpha_dummy_451;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0464 f)
                                              0)))) (TAlphaVar.there (show
                                      (nb068_alpha_dummy_408) ≠ (nb068_alpha_dummy_455) from (by
                                        unfold nb068_alpha_dummy_455;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0466)
                                                0)))) (show (nb068_alpha_dummy_410 f) ≠
                                        (nb068_alpha_dummy_456 f) from (by
                                        unfold nb068_alpha_dummy_456;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0467 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068_alpha_dummy_408) ≠ (nb068_alpha_dummy_453) from
                                        (by
                                          unfold nb068_alpha_dummy_453;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0463)
                                                  0)))) (show (nb068_alpha_dummy_410 f) ≠
        (nb068_alpha_dummy_454 f) from (by
                                          unfold nb068_alpha_dummy_454;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0465 f) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_408))).fv ∪
                                    ((Class.cv (nb068_alpha_dummy_407))).fv) (by decide))
                                (freshVar_injective (((Class.cv (nb068_alpha_dummy_410 f))).fv ∪
                                    ((Class.cv (nb068_alpha_dummy_409 f))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb068_alpha_dummy_450) ≠
        (nb068_alpha_dummy_457) from (by
          unfold nb068_alpha_dummy_457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0468) 0)))) (show (nb068_alpha_dummy_452 f) ≠
        (nb068_alpha_dummy_459 f) from (by
          unfold nb068_alpha_dummy_459;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0469 f) 0)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_450) ≠ (nb068_alpha_dummy_458) from (by
          unfold nb068_alpha_dummy_458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0468) 1)))) (show (nb068_alpha_dummy_452 f) ≠
        (nb068_alpha_dummy_460 f) from (by
          unfold nb068_alpha_dummy_460;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0469 f) 1)))) (TAlphaVar.here _ _ _)))))
                                  (nb068_split_alpha_0105 x y f)))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb068_alpha_dummy_408) ≠ (nb068_alpha_dummy_450) from (by
                                    unfold nb068_alpha_dummy_450;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0462) 1)))) (show
                                  (nb068_alpha_dummy_410 f) ≠ (nb068_alpha_dummy_452 f) from (by
                                    unfold nb068_alpha_dummy_452;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0464 f)
                                            1)))) (TAlphaVar.there
                                  (show (nb068_alpha_dummy_408) ≠ (nb068_alpha_dummy_449) from
                                    (by
                                      unfold nb068_alpha_dummy_449;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0462)
                                              0)))) (show
                                    (nb068_alpha_dummy_410 f) ≠ (nb068_alpha_dummy_451 f) from
                                    (by
                                      unfold nb068_alpha_dummy_451;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0464 f)
                                              0)))) (TAlphaVar.there (show
                                      (nb068_alpha_dummy_408) ≠ (nb068_alpha_dummy_455) from (by
                                        unfold nb068_alpha_dummy_455;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0466)
                                                0)))) (show (nb068_alpha_dummy_410 f) ≠
                                        (nb068_alpha_dummy_456 f) from (by
                                        unfold nb068_alpha_dummy_456;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0467 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068_alpha_dummy_408) ≠ (nb068_alpha_dummy_453) from
                                        (by
                                          unfold nb068_alpha_dummy_453;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0463)
                                                  0)))) (show (nb068_alpha_dummy_410 f) ≠
        (nb068_alpha_dummy_454 f) from (by
                                          unfold nb068_alpha_dummy_454;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0465 f) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_408))).fv ∪
                                    ((Class.cv (nb068_alpha_dummy_407))).fv) (by decide))
                                (freshVar_injective (((Class.cv (nb068_alpha_dummy_410 f))).fv ∪
                                    ((Class.cv (nb068_alpha_dummy_409 f))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb068_alpha_dummy_450) ≠
        (nb068_alpha_dummy_457) from (by
          unfold nb068_alpha_dummy_457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0468) 0)))) (show (nb068_alpha_dummy_452 f) ≠
        (nb068_alpha_dummy_459 f) from (by
          unfold nb068_alpha_dummy_459;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0469 f) 0)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_450) ≠ (nb068_alpha_dummy_458) from (by
          unfold nb068_alpha_dummy_458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0468) 1)))) (show (nb068_alpha_dummy_452 f) ≠
        (nb068_alpha_dummy_460 f) from (by
          unfold nb068_alpha_dummy_460;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0469 f) 1)))) (TAlphaVar.here _ _ _)))))
                                  (nb068_split_alpha_0105 x y f)))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.all (nb068_split_alpha_0108 x y f)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.all (nb068_split_alpha_0108 x y f))))))))))))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (Ne.symm
                    (show (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_129) from (by
                        unfold nb068_alpha_dummy_129;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0124) 0)))))
                  (Ne.symm (show (nb068_alpha_dummy_128 f) ≠ (nb068_alpha_dummy_130 f) from (by
                        unfold nb068_alpha_dummy_130;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0125 f) 0)))))
                  (TAlphaVar.there (Ne.symm
                      (show (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_129) from (by
                          unfold nb068_alpha_dummy_129;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0122) 0))))) (Ne.symm
                      (show (nb068_alpha_dummy_127 f) ≠ (nb068_alpha_dummy_130 f) from (by
                          unfold nb068_alpha_dummy_130;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0123 f) 0)))))
                    (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0114 x y f)))))
            (TAlphaWff.classMem (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0120 x y f)))) (TAlphaClass.cv
                (TAlphaVar.there (show (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_126) from
                    (by
                      unfold nb068_alpha_dummy_126;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0212) 1))))
                  (show f ≠ (nb068_alpha_dummy_128 f) from (by
                      unfold nb068_alpha_dummy_128;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0213 f) 1))))
                  (TAlphaVar.there (show (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_125) from
                      (by
                        unfold nb068_alpha_dummy_125;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0212) 0))))
                    (show f ≠ (nb068_alpha_dummy_127 f) from (by
                        unfold nb068_alpha_dummy_127;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0213 f) 0)))) (TAlphaVar.there
                      (show (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_129) from (by
                          unfold nb068_alpha_dummy_129;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0210) 0))))
                      (show f ≠ (nb068_alpha_dummy_130 f) from (by
                          unfold nb068_alpha_dummy_130;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0211 f) 0))))
                      (TAlphaVar.there
                        (show (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_408) from (by
                            unfold nb068_alpha_dummy_408;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0510) 1))))
                        (show f ≠ (nb068_alpha_dummy_410 f) from (by
                            unfold nb068_alpha_dummy_410;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0511 f) 1))))
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_407) from (by
                              unfold nb068_alpha_dummy_407;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0510) 0))))
                          (show f ≠ (nb068_alpha_dummy_409 f) from (by
                              unfold nb068_alpha_dummy_409;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0511 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_411) from (by
                                unfold nb068_alpha_dummy_411;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0508) 0))))
                            (show f ≠ (nb068_alpha_dummy_412 f) from (by
                                unfold nb068_alpha_dummy_412;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0509 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_329) from (by
                                  unfold nb068_alpha_dummy_329;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0504) 2))))
                              (show f ≠ (nb068_alpha_dummy_332 f) from (by
                                  unfold nb068_alpha_dummy_332;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0506 f) 2))))
                              (TAlphaVar.there
                                (show (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_328) from (by
                                    unfold nb068_alpha_dummy_328;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0504) 1))))
                                (show f ≠ (nb068_alpha_dummy_331 f) from (by
                                    unfold nb068_alpha_dummy_331;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0506 f)
                                            1)))) (TAlphaVar.there
                                  (show (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_327) from
                                    (by
                                      unfold nb068_alpha_dummy_327;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0504)
                                              0)))) (show f ≠ (nb068_alpha_dummy_330 f) from (by
                                      unfold nb068_alpha_dummy_330;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0506 f)
                                              0)))) (TAlphaVar.there (show
                                      (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_333) from (by
                                        unfold nb068_alpha_dummy_333;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0505)
                                                0)))) (show f ≠ (nb068_alpha_dummy_334 f) from
                                      (by
                                        unfold nb068_alpha_dummy_334;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0507 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_325) from
                                        (by
                                          unfold nb068_alpha_dummy_325;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0502)
                                                  0)))) (show f ≠ (nb068_alpha_dummy_326 f) from
                                        (by
                                          unfold nb068_alpha_dummy_326;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0503 f) 0))))
                                      (TAlphaVar.there (show (nb068_alpha_dummy_000) ≠
        (nb068_alpha_dummy_323) from (by
          unfold nb068_alpha_dummy_323;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0500) 0)))) (show f ≠ (nb068_alpha_dummy_324 f) from (by
          unfold nb068_alpha_dummy_324;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0501 f) 0)))) (TAlphaVar.here _ _ _))))))))))))))))))))

@[expose]
noncomputable def nb068_split_alpha_0122 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)),
        ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)),
        ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)),
        ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
        ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
        ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
        ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
        ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
        ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classEq (Class.cv (nb068_alpha_dummy_411))
          (syn_cop (Class.cv (nb068_alpha_dummy_407)) (Class.cv (nb068_alpha_dummy_408))))
        (Wff.neg (syn_wbr (Class.cv (nb068_alpha_dummy_408))
            (syn_ccnv (Class.cv (nb068_alpha_dummy_000))) (Class.cv (nb068_alpha_dummy_407)))))
      (Wff.imp (Wff.classEq (Class.cv (nb068_alpha_dummy_412 f))
          (syn_cop (Class.cv (nb068_alpha_dummy_409 f)) (Class.cv (nb068_alpha_dummy_410 f))))
        (Wff.neg (syn_wbr (Class.cv (nb068_alpha_dummy_410 f)) (syn_ccnv (Class.cv f))
            (Class.cv (nb068_alpha_dummy_409 f))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
            (show (nb068_alpha_dummy_408) ≠ (nb068_alpha_dummy_411) from (by
                unfold nb068_alpha_dummy_411;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0422) 0))))) (Ne.symm
            (show (nb068_alpha_dummy_410 f) ≠ (nb068_alpha_dummy_412 f) from (by
                unfold nb068_alpha_dummy_412;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0423 f) 0)))))
          (TAlphaVar.there (Ne.symm (show (nb068_alpha_dummy_407) ≠ (nb068_alpha_dummy_411) from
                (by
                  unfold nb068_alpha_dummy_411;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0420) 0)))))
            (Ne.symm (show (nb068_alpha_dummy_409 f) ≠ (nb068_alpha_dummy_412 f) from (by
                  unfold nb068_alpha_dummy_412;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0421 f) 0)))))
            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb068_alpha_dummy_407) ≠ (nb068_alpha_dummy_414) from
                                    (by
                                      unfold nb068_alpha_dummy_414;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0424)
                                              1)))) (show
                                    (nb068_alpha_dummy_409 f) ≠ (nb068_alpha_dummy_416 f) from
                                    (by
                                      unfold nb068_alpha_dummy_416;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0426 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb068_alpha_dummy_407) ≠ (nb068_alpha_dummy_413) from (by
                                        unfold nb068_alpha_dummy_413;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0424)
                                                0)))) (show (nb068_alpha_dummy_409 f) ≠
                                        (nb068_alpha_dummy_415 f) from (by
                                        unfold nb068_alpha_dummy_415;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0426 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068_alpha_dummy_407) ≠ (nb068_alpha_dummy_419) from
                                        (by
                                          unfold nb068_alpha_dummy_419;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0428)
                                                  0)))) (show (nb068_alpha_dummy_409 f) ≠
        (nb068_alpha_dummy_420 f) from (by
                                          unfold nb068_alpha_dummy_420;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0429 f) 0))))
                                      (TAlphaVar.there (show (nb068_alpha_dummy_407) ≠
        (nb068_alpha_dummy_417) from (by
          unfold nb068_alpha_dummy_417;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0425) 0)))) (show (nb068_alpha_dummy_409 f) ≠
        (nb068_alpha_dummy_418 f) from (by
          unfold nb068_alpha_dummy_418;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0427 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv) (by decide)) (freshVar_injective
        (((syn_ccnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb068_alpha_dummy_407))).fv ∪
                                      ((Class.cv (nb068_alpha_dummy_408))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb068_alpha_dummy_409 f))).fv ∪
                                      ((Class.cv (nb068_alpha_dummy_410 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb068_alpha_dummy_414) ≠
        (nb068_alpha_dummy_421) from (by
          unfold nb068_alpha_dummy_421;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0430) 0)))) (show (nb068_alpha_dummy_416 f) ≠
        (nb068_alpha_dummy_423 f) from (by
          unfold nb068_alpha_dummy_423;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0431 f) 0)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_414) ≠ (nb068_alpha_dummy_422) from (by
          unfold nb068_alpha_dummy_422;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0430) 1)))) (show (nb068_alpha_dummy_416 f) ≠
        (nb068_alpha_dummy_424 f) from (by
          unfold nb068_alpha_dummy_424;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0431 f) 1)))) (TAlphaVar.here _ _ _)))))
                                    (nb068_split_alpha_0100 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb068_alpha_dummy_407) ≠ (nb068_alpha_dummy_414) from
                                    (by
                                      unfold nb068_alpha_dummy_414;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0424)
                                              1)))) (show
                                    (nb068_alpha_dummy_409 f) ≠ (nb068_alpha_dummy_416 f) from
                                    (by
                                      unfold nb068_alpha_dummy_416;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0426 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb068_alpha_dummy_407) ≠ (nb068_alpha_dummy_413) from (by
                                        unfold nb068_alpha_dummy_413;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0424)
                                                0)))) (show (nb068_alpha_dummy_409 f) ≠
                                        (nb068_alpha_dummy_415 f) from (by
                                        unfold nb068_alpha_dummy_415;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0426 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068_alpha_dummy_407) ≠ (nb068_alpha_dummy_419) from
                                        (by
                                          unfold nb068_alpha_dummy_419;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0428)
                                                  0)))) (show (nb068_alpha_dummy_409 f) ≠
        (nb068_alpha_dummy_420 f) from (by
                                          unfold nb068_alpha_dummy_420;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0429 f) 0))))
                                      (TAlphaVar.there (show (nb068_alpha_dummy_407) ≠
        (nb068_alpha_dummy_417) from (by
          unfold nb068_alpha_dummy_417;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0425) 0)))) (show (nb068_alpha_dummy_409 f) ≠
        (nb068_alpha_dummy_418 f) from (by
          unfold nb068_alpha_dummy_418;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0427 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv) (by decide)) (freshVar_injective
        (((syn_ccnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb068_alpha_dummy_407))).fv ∪
                                      ((Class.cv (nb068_alpha_dummy_408))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb068_alpha_dummy_409 f))).fv ∪
                                      ((Class.cv (nb068_alpha_dummy_410 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb068_alpha_dummy_414) ≠
        (nb068_alpha_dummy_421) from (by
          unfold nb068_alpha_dummy_421;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0430) 0)))) (show (nb068_alpha_dummy_416 f) ≠
        (nb068_alpha_dummy_423 f) from (by
          unfold nb068_alpha_dummy_423;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0431 f) 0)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_414) ≠ (nb068_alpha_dummy_422) from (by
          unfold nb068_alpha_dummy_422;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0430) 1)))) (show (nb068_alpha_dummy_416 f) ≠
        (nb068_alpha_dummy_424 f) from (by
          unfold nb068_alpha_dummy_424;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0431 f) 1)))) (TAlphaVar.here _ _ _)))))
                                    (nb068_split_alpha_0100 x y f)))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0103 x y f)))))))))
    (TAlphaWff.neg (nb068_split_alpha_0121 x y f)))

@[expose]
noncomputable def nb068_split_alpha_0123 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_501), (nb068_alpha_dummy_504 f)),
        ((nb068_alpha_dummy_500), (nb068_alpha_dummy_503 f)),
        ((nb068_alpha_dummy_499), (nb068_alpha_dummy_502 f)),
        ((nb068_alpha_dummy_497), (nb068_alpha_dummy_498 f)),
        ((nb068_alpha_dummy_493), (nb068_alpha_dummy_495 f)),
        ((nb068_alpha_dummy_494), (nb068_alpha_dummy_496 f)),
        ((nb068_alpha_dummy_486), (nb068_alpha_dummy_488 f)),
        ((nb068_alpha_dummy_485), (nb068_alpha_dummy_487 f)),
        ((nb068_alpha_dummy_491), (nb068_alpha_dummy_492 f)),
        ((nb068_alpha_dummy_489), (nb068_alpha_dummy_490 f)),
        ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
        ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
        ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
        ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
        ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
        ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb068_alpha_dummy_500)) (Class.cv (nb068_alpha_dummy_501)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_499))
            (syn_cun (Class.cv (nb068_alpha_dummy_500)) (Class.cv (nb068_alpha_dummy_501))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_503 f))
            (Class.cv (nb068_alpha_dummy_504 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_502 f))
            (syn_cun (Class.cv (nb068_alpha_dummy_503 f))
              (Class.cv (nb068_alpha_dummy_504 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_500) ≠ (nb068_alpha_dummy_507) from (by
                              unfold nb068_alpha_dummy_507;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0526) 0))))
                          (show (nb068_alpha_dummy_503 f) ≠ (nb068_alpha_dummy_508 f) from (by
                              unfold nb068_alpha_dummy_508;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0527 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_500) ≠ (nb068_alpha_dummy_505) from (by
                                unfold nb068_alpha_dummy_505;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0524) 0))))
                            (show (nb068_alpha_dummy_503 f) ≠ (nb068_alpha_dummy_506 f) from (by
                                unfold nb068_alpha_dummy_506;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0525 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_495 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_501) ≠ (nb068_alpha_dummy_507) from (by
                              unfold nb068_alpha_dummy_507;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0530) 0))))
                          (show (nb068_alpha_dummy_504 f) ≠ (nb068_alpha_dummy_508 f) from (by
                              unfold nb068_alpha_dummy_508;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0531 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_501) ≠ (nb068_alpha_dummy_505) from (by
                                unfold nb068_alpha_dummy_505;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0528) 0))))
                            (show (nb068_alpha_dummy_504 f) ≠ (nb068_alpha_dummy_506 f) from (by
                                unfold nb068_alpha_dummy_506;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0529 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_500) ≠ (nb068_alpha_dummy_507) from (by
                              unfold nb068_alpha_dummy_507;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0526) 0))))
                          (show (nb068_alpha_dummy_503 f) ≠ (nb068_alpha_dummy_508 f) from (by
                              unfold nb068_alpha_dummy_508;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0527 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_500) ≠ (nb068_alpha_dummy_505) from (by
                                unfold nb068_alpha_dummy_505;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0524) 0))))
                            (show (nb068_alpha_dummy_503 f) ≠ (nb068_alpha_dummy_506 f) from (by
                                unfold nb068_alpha_dummy_506;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0525 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_495 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_501) ≠ (nb068_alpha_dummy_507) from (by
                              unfold nb068_alpha_dummy_507;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0530) 0))))
                          (show (nb068_alpha_dummy_504 f) ≠ (nb068_alpha_dummy_508 f) from (by
                              unfold nb068_alpha_dummy_508;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0531 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_501) ≠ (nb068_alpha_dummy_505) from (by
                                unfold nb068_alpha_dummy_505;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0528) 0))))
                            (show (nb068_alpha_dummy_504 f) ≠ (nb068_alpha_dummy_506 f) from (by
                                unfold nb068_alpha_dummy_506;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0529 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb068_alpha_dummy_501), (nb068_alpha_dummy_504 f)),
          ((nb068_alpha_dummy_500), (nb068_alpha_dummy_503 f)),
          ((nb068_alpha_dummy_499), (nb068_alpha_dummy_502 f)),
          ((nb068_alpha_dummy_497), (nb068_alpha_dummy_498 f)),
          ((nb068_alpha_dummy_493), (nb068_alpha_dummy_495 f)),
          ((nb068_alpha_dummy_494), (nb068_alpha_dummy_496 f)),
          ((nb068_alpha_dummy_486), (nb068_alpha_dummy_488 f)),
          ((nb068_alpha_dummy_485), (nb068_alpha_dummy_487 f)),
          ((nb068_alpha_dummy_491), (nb068_alpha_dummy_492 f)),
          ((nb068_alpha_dummy_489), (nb068_alpha_dummy_490 f)),
          ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
          ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
          ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
          ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
          ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
          ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
          ((nb068_alpha_dummy_001), x),
          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068_alpha_dummy_495 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_495 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_500) ≠ (nb068_alpha_dummy_511) from (by
                                unfold nb068_alpha_dummy_511;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0534) 0))))
                            (show (nb068_alpha_dummy_503 f) ≠ (nb068_alpha_dummy_512 f) from (by
                                unfold nb068_alpha_dummy_512;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0535 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_500) ≠ (nb068_alpha_dummy_509) from (by
                                  unfold nb068_alpha_dummy_509;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0532) 0))))
                              (show (nb068_alpha_dummy_503 f) ≠ (nb068_alpha_dummy_510 f) from
                                (by
                                  unfold nb068_alpha_dummy_510;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0533 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_495 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_500) ≠ (nb068_alpha_dummy_511) from (by
                                unfold nb068_alpha_dummy_511;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0534) 0))))
                            (show (nb068_alpha_dummy_503 f) ≠ (nb068_alpha_dummy_512 f) from (by
                                unfold nb068_alpha_dummy_512;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0535 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_500) ≠ (nb068_alpha_dummy_509) from (by
                                  unfold nb068_alpha_dummy_509;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0532) 0))))
                              (show (nb068_alpha_dummy_503 f) ≠ (nb068_alpha_dummy_510 f) from
                                (by
                                  unfold nb068_alpha_dummy_510;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0533 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_495 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_501) ≠ (nb068_alpha_dummy_513) from (by
                                unfold nb068_alpha_dummy_513;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0538) 0))))
                            (show (nb068_alpha_dummy_504 f) ≠ (nb068_alpha_dummy_514 f) from (by
                                unfold nb068_alpha_dummy_514;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0539 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_501) ≠ (nb068_alpha_dummy_509) from (by
                                  unfold nb068_alpha_dummy_509;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0536) 0))))
                              (show (nb068_alpha_dummy_504 f) ≠ (nb068_alpha_dummy_510 f) from
                                (by
                                  unfold nb068_alpha_dummy_510;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0537 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_501) ≠ (nb068_alpha_dummy_513) from (by
                                unfold nb068_alpha_dummy_513;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0538) 0))))
                            (show (nb068_alpha_dummy_504 f) ≠ (nb068_alpha_dummy_514 f) from (by
                                unfold nb068_alpha_dummy_514;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0539 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_501) ≠ (nb068_alpha_dummy_509) from (by
                                  unfold nb068_alpha_dummy_509;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0536) 0))))
                              (show (nb068_alpha_dummy_504 f) ≠ (nb068_alpha_dummy_510 f) from
                                (by
                                  unfold nb068_alpha_dummy_510;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0537 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part047`. -/


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
noncomputable def nb068_split_alpha_0124 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_493), (nb068_alpha_dummy_495 f)),
        ((nb068_alpha_dummy_494), (nb068_alpha_dummy_496 f)),
        ((nb068_alpha_dummy_486), (nb068_alpha_dummy_488 f)),
        ((nb068_alpha_dummy_485), (nb068_alpha_dummy_487 f)),
        ((nb068_alpha_dummy_491), (nb068_alpha_dummy_492 f)),
        ((nb068_alpha_dummy_489), (nb068_alpha_dummy_490 f)),
        ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
        ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
        ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
        ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
        ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
        ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_493))
          (Class.cv (nb068_alpha_dummy_486))) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_494))
            (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_493)) (syn_cnnc))
              (syn_cplc (Class.cv (nb068_alpha_dummy_493)) (syn_c1c))
              (Class.cv (nb068_alpha_dummy_493))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_495 f))
          (Class.cv (nb068_alpha_dummy_488 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_496 f))
            (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_495 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb068_alpha_dummy_495 f)) (syn_c1c))
              (Class.cv (nb068_alpha_dummy_495 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068_alpha_dummy_486) ≠ (nb068_alpha_dummy_493) from (by
              unfold nb068_alpha_dummy_493;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0518) 0))))
          (show (nb068_alpha_dummy_488 f) ≠ (nb068_alpha_dummy_495 f) from (by
              unfold nb068_alpha_dummy_495;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0519 f) 0))))
          (TAlphaVar.there (show (nb068_alpha_dummy_486) ≠ (nb068_alpha_dummy_494) from (by
                unfold nb068_alpha_dummy_494;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0518) 1))))
            (show (nb068_alpha_dummy_488 f) ≠ (nb068_alpha_dummy_496 f) from (by
                unfold nb068_alpha_dummy_496;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0519 f) 1))))
            (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_486))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_488 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068_alpha_dummy_493) ≠ (nb068_alpha_dummy_500) from (by
                                  unfold nb068_alpha_dummy_500;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0522) 1))))
                              (show (nb068_alpha_dummy_495 f) ≠ (nb068_alpha_dummy_503 f) from
                                (by
                                  unfold nb068_alpha_dummy_503;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0523 f) 1))))
                              (TAlphaVar.there
                                (show (nb068_alpha_dummy_493) ≠ (nb068_alpha_dummy_499) from (by
                                    unfold nb068_alpha_dummy_499;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0522) 0)))) (show
                                  (nb068_alpha_dummy_495 f) ≠ (nb068_alpha_dummy_502 f) from (by
                                    unfold nb068_alpha_dummy_502;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0523 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb068_alpha_dummy_493) ≠ (nb068_alpha_dummy_497) from
                                    (by
                                      unfold nb068_alpha_dummy_497;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0520)
                                              0)))) (show
                                    (nb068_alpha_dummy_495 f) ≠ (nb068_alpha_dummy_498 f) from
                                    (by
                                      unfold nb068_alpha_dummy_498;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0521 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb068_alpha_dummy_501), (nb068_alpha_dummy_504 f)),
                                  ((nb068_alpha_dummy_500), (nb068_alpha_dummy_503 f)),
                                  ((nb068_alpha_dummy_499), (nb068_alpha_dummy_502 f)),
                                  ((nb068_alpha_dummy_497), (nb068_alpha_dummy_498 f)),
                                  ((nb068_alpha_dummy_493), (nb068_alpha_dummy_495 f)),
                                  ((nb068_alpha_dummy_494), (nb068_alpha_dummy_496 f)),
                                  ((nb068_alpha_dummy_486), (nb068_alpha_dummy_488 f)),
                                  ((nb068_alpha_dummy_485), (nb068_alpha_dummy_487 f)),
                                  ((nb068_alpha_dummy_491), (nb068_alpha_dummy_492 f)),
                                  ((nb068_alpha_dummy_489), (nb068_alpha_dummy_490 f)),
                                  ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
                                  ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
                                  ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
                                  ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
                                  ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
                                  ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
                                  ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                                  ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003),
                                    (nb068_alpha_dummy_004 x y f))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb068_split_alpha_0123 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb068_alpha_dummy_493) ≠ (nb068_alpha_dummy_497) from (by
                          unfold nb068_alpha_dummy_497;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0520) 0))))
                      (show (nb068_alpha_dummy_495 f) ≠ (nb068_alpha_dummy_498 f) from (by
                          unfold nb068_alpha_dummy_498;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0521 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb068_alpha_dummy_497), (nb068_alpha_dummy_498 f)),
                      ((nb068_alpha_dummy_493), (nb068_alpha_dummy_495 f)),
                      ((nb068_alpha_dummy_494), (nb068_alpha_dummy_496 f)),
                      ((nb068_alpha_dummy_486), (nb068_alpha_dummy_488 f)),
                      ((nb068_alpha_dummy_485), (nb068_alpha_dummy_487 f)),
                      ((nb068_alpha_dummy_491), (nb068_alpha_dummy_492 f)),
                      ((nb068_alpha_dummy_489), (nb068_alpha_dummy_490 f)),
                      ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
                      ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
                      ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
                      ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
                      ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
                      ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
                      ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                      ((nb068_alpha_dummy_001), x),
                      ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068_alpha_dummy_493) ≠ (nb068_alpha_dummy_497) from
                      (by
                        unfold nb068_alpha_dummy_497;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0520) 0))))
                    (show (nb068_alpha_dummy_495 f) ≠ (nb068_alpha_dummy_498 f) from (by
                        unfold nb068_alpha_dummy_498;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0521 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068_alpha_dummy_493) ≠ (nb068_alpha_dummy_497) from (by
                          unfold nb068_alpha_dummy_497;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0520) 0))))
                      (show (nb068_alpha_dummy_495 f) ≠ (nb068_alpha_dummy_498 f) from (by
                          unfold nb068_alpha_dummy_498;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0521 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb068_alpha_dummy_497), (nb068_alpha_dummy_498 f)),
                      ((nb068_alpha_dummy_493), (nb068_alpha_dummy_495 f)),
                      ((nb068_alpha_dummy_494), (nb068_alpha_dummy_496 f)),
                      ((nb068_alpha_dummy_486), (nb068_alpha_dummy_488 f)),
                      ((nb068_alpha_dummy_485), (nb068_alpha_dummy_487 f)),
                      ((nb068_alpha_dummy_491), (nb068_alpha_dummy_492 f)),
                      ((nb068_alpha_dummy_489), (nb068_alpha_dummy_490 f)),
                      ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
                      ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
                      ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
                      ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
                      ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
                      ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
                      ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                      ((nb068_alpha_dummy_001), x),
                      ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb068_split_alpha_0125 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_501), (nb068_alpha_dummy_504 f)),
        ((nb068_alpha_dummy_500), (nb068_alpha_dummy_503 f)),
        ((nb068_alpha_dummy_499), (nb068_alpha_dummy_502 f)),
        ((nb068_alpha_dummy_497), (nb068_alpha_dummy_498 f)),
        ((nb068_alpha_dummy_493), (nb068_alpha_dummy_495 f)),
        ((nb068_alpha_dummy_494), (nb068_alpha_dummy_496 f)),
        ((nb068_alpha_dummy_519), (nb068_alpha_dummy_520 f)),
        ((nb068_alpha_dummy_517), (nb068_alpha_dummy_518 f)),
        ((nb068_alpha_dummy_486), (nb068_alpha_dummy_488 f)),
        ((nb068_alpha_dummy_485), (nb068_alpha_dummy_487 f)),
        ((nb068_alpha_dummy_515), (nb068_alpha_dummy_516 f)),
        ((nb068_alpha_dummy_489), (nb068_alpha_dummy_490 f)),
        ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
        ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
        ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
        ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
        ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
        ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb068_alpha_dummy_500)) (Class.cv (nb068_alpha_dummy_501)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_499))
            (syn_cun (Class.cv (nb068_alpha_dummy_500)) (Class.cv (nb068_alpha_dummy_501))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_503 f))
            (Class.cv (nb068_alpha_dummy_504 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_502 f))
            (syn_cun (Class.cv (nb068_alpha_dummy_503 f))
              (Class.cv (nb068_alpha_dummy_504 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_500) ≠ (nb068_alpha_dummy_507) from (by
                              unfold nb068_alpha_dummy_507;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0526) 0))))
                          (show (nb068_alpha_dummy_503 f) ≠ (nb068_alpha_dummy_508 f) from (by
                              unfold nb068_alpha_dummy_508;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0527 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_500) ≠ (nb068_alpha_dummy_505) from (by
                                unfold nb068_alpha_dummy_505;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0524) 0))))
                            (show (nb068_alpha_dummy_503 f) ≠ (nb068_alpha_dummy_506 f) from (by
                                unfold nb068_alpha_dummy_506;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0525 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_495 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_501) ≠ (nb068_alpha_dummy_507) from (by
                              unfold nb068_alpha_dummy_507;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0530) 0))))
                          (show (nb068_alpha_dummy_504 f) ≠ (nb068_alpha_dummy_508 f) from (by
                              unfold nb068_alpha_dummy_508;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0531 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_501) ≠ (nb068_alpha_dummy_505) from (by
                                unfold nb068_alpha_dummy_505;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0528) 0))))
                            (show (nb068_alpha_dummy_504 f) ≠ (nb068_alpha_dummy_506 f) from (by
                                unfold nb068_alpha_dummy_506;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0529 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_500) ≠ (nb068_alpha_dummy_507) from (by
                              unfold nb068_alpha_dummy_507;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0526) 0))))
                          (show (nb068_alpha_dummy_503 f) ≠ (nb068_alpha_dummy_508 f) from (by
                              unfold nb068_alpha_dummy_508;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0527 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_500) ≠ (nb068_alpha_dummy_505) from (by
                                unfold nb068_alpha_dummy_505;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0524) 0))))
                            (show (nb068_alpha_dummy_503 f) ≠ (nb068_alpha_dummy_506 f) from (by
                                unfold nb068_alpha_dummy_506;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0525 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_495 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_501) ≠ (nb068_alpha_dummy_507) from (by
                              unfold nb068_alpha_dummy_507;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0530) 0))))
                          (show (nb068_alpha_dummy_504 f) ≠ (nb068_alpha_dummy_508 f) from (by
                              unfold nb068_alpha_dummy_508;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0531 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_501) ≠ (nb068_alpha_dummy_505) from (by
                                unfold nb068_alpha_dummy_505;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0528) 0))))
                            (show (nb068_alpha_dummy_504 f) ≠ (nb068_alpha_dummy_506 f) from (by
                                unfold nb068_alpha_dummy_506;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0529 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb068_alpha_dummy_501), (nb068_alpha_dummy_504 f)),
          ((nb068_alpha_dummy_500), (nb068_alpha_dummy_503 f)),
          ((nb068_alpha_dummy_499), (nb068_alpha_dummy_502 f)),
          ((nb068_alpha_dummy_497), (nb068_alpha_dummy_498 f)),
          ((nb068_alpha_dummy_493), (nb068_alpha_dummy_495 f)),
          ((nb068_alpha_dummy_494), (nb068_alpha_dummy_496 f)),
          ((nb068_alpha_dummy_519), (nb068_alpha_dummy_520 f)),
          ((nb068_alpha_dummy_517), (nb068_alpha_dummy_518 f)),
          ((nb068_alpha_dummy_486), (nb068_alpha_dummy_488 f)),
          ((nb068_alpha_dummy_485), (nb068_alpha_dummy_487 f)),
          ((nb068_alpha_dummy_515), (nb068_alpha_dummy_516 f)),
          ((nb068_alpha_dummy_489), (nb068_alpha_dummy_490 f)),
          ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
          ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
          ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
          ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
          ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
          ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
          ((nb068_alpha_dummy_001), x),
          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068_alpha_dummy_495 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_495 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_500) ≠ (nb068_alpha_dummy_511) from (by
                                unfold nb068_alpha_dummy_511;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0534) 0))))
                            (show (nb068_alpha_dummy_503 f) ≠ (nb068_alpha_dummy_512 f) from (by
                                unfold nb068_alpha_dummy_512;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0535 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_500) ≠ (nb068_alpha_dummy_509) from (by
                                  unfold nb068_alpha_dummy_509;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0532) 0))))
                              (show (nb068_alpha_dummy_503 f) ≠ (nb068_alpha_dummy_510 f) from
                                (by
                                  unfold nb068_alpha_dummy_510;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0533 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_495 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_500) ≠ (nb068_alpha_dummy_511) from (by
                                unfold nb068_alpha_dummy_511;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0534) 0))))
                            (show (nb068_alpha_dummy_503 f) ≠ (nb068_alpha_dummy_512 f) from (by
                                unfold nb068_alpha_dummy_512;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0535 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_500) ≠ (nb068_alpha_dummy_509) from (by
                                  unfold nb068_alpha_dummy_509;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0532) 0))))
                              (show (nb068_alpha_dummy_503 f) ≠ (nb068_alpha_dummy_510 f) from
                                (by
                                  unfold nb068_alpha_dummy_510;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0533 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_495 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_501) ≠ (nb068_alpha_dummy_513) from (by
                                unfold nb068_alpha_dummy_513;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0538) 0))))
                            (show (nb068_alpha_dummy_504 f) ≠ (nb068_alpha_dummy_514 f) from (by
                                unfold nb068_alpha_dummy_514;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0539 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_501) ≠ (nb068_alpha_dummy_509) from (by
                                  unfold nb068_alpha_dummy_509;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0536) 0))))
                              (show (nb068_alpha_dummy_504 f) ≠ (nb068_alpha_dummy_510 f) from
                                (by
                                  unfold nb068_alpha_dummy_510;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0537 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_501) ≠ (nb068_alpha_dummy_513) from (by
                                unfold nb068_alpha_dummy_513;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0538) 0))))
                            (show (nb068_alpha_dummy_504 f) ≠ (nb068_alpha_dummy_514 f) from (by
                                unfold nb068_alpha_dummy_514;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0539 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_501) ≠ (nb068_alpha_dummy_509) from (by
                                  unfold nb068_alpha_dummy_509;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0536) 0))))
                              (show (nb068_alpha_dummy_504 f) ≠ (nb068_alpha_dummy_510 f) from
                                (by
                                  unfold nb068_alpha_dummy_510;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0537 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb068_split_alpha_0126 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_493), (nb068_alpha_dummy_495 f)),
        ((nb068_alpha_dummy_494), (nb068_alpha_dummy_496 f)),
        ((nb068_alpha_dummy_519), (nb068_alpha_dummy_520 f)),
        ((nb068_alpha_dummy_517), (nb068_alpha_dummy_518 f)),
        ((nb068_alpha_dummy_486), (nb068_alpha_dummy_488 f)),
        ((nb068_alpha_dummy_485), (nb068_alpha_dummy_487 f)),
        ((nb068_alpha_dummy_515), (nb068_alpha_dummy_516 f)),
        ((nb068_alpha_dummy_489), (nb068_alpha_dummy_490 f)),
        ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
        ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
        ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
        ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
        ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
        ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_493))
          (Class.cv (nb068_alpha_dummy_486))) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_494))
            (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_493)) (syn_cnnc))
              (syn_cplc (Class.cv (nb068_alpha_dummy_493)) (syn_c1c))
              (Class.cv (nb068_alpha_dummy_493))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_495 f))
          (Class.cv (nb068_alpha_dummy_488 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_496 f))
            (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_495 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb068_alpha_dummy_495 f)) (syn_c1c))
              (Class.cv (nb068_alpha_dummy_495 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068_alpha_dummy_486) ≠ (nb068_alpha_dummy_493) from (by
              unfold nb068_alpha_dummy_493;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0518) 0))))
          (show (nb068_alpha_dummy_488 f) ≠ (nb068_alpha_dummy_495 f) from (by
              unfold nb068_alpha_dummy_495;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0519 f) 0))))
          (TAlphaVar.there (show (nb068_alpha_dummy_486) ≠ (nb068_alpha_dummy_494) from (by
                unfold nb068_alpha_dummy_494;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0518) 1))))
            (show (nb068_alpha_dummy_488 f) ≠ (nb068_alpha_dummy_496 f) from (by
                unfold nb068_alpha_dummy_496;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0519 f) 1))))
            (TAlphaVar.there (show (nb068_alpha_dummy_486) ≠ (nb068_alpha_dummy_519) from (by
                  unfold nb068_alpha_dummy_519;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0548) 0))))
              (show (nb068_alpha_dummy_488 f) ≠ (nb068_alpha_dummy_520 f) from (by
                  unfold nb068_alpha_dummy_520;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0549 f) 0))))
              (TAlphaVar.there (show (nb068_alpha_dummy_486) ≠ (nb068_alpha_dummy_517) from (by
                    unfold nb068_alpha_dummy_517;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0546) 0))))
                (show (nb068_alpha_dummy_488 f) ≠ (nb068_alpha_dummy_518 f) from (by
                    unfold nb068_alpha_dummy_518;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0547 f) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_486))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_488 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068_alpha_dummy_493) ≠ (nb068_alpha_dummy_500) from (by
                                  unfold nb068_alpha_dummy_500;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0522) 1))))
                              (show (nb068_alpha_dummy_495 f) ≠ (nb068_alpha_dummy_503 f) from
                                (by
                                  unfold nb068_alpha_dummy_503;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0523 f) 1))))
                              (TAlphaVar.there
                                (show (nb068_alpha_dummy_493) ≠ (nb068_alpha_dummy_499) from (by
                                    unfold nb068_alpha_dummy_499;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0522) 0)))) (show
                                  (nb068_alpha_dummy_495 f) ≠ (nb068_alpha_dummy_502 f) from (by
                                    unfold nb068_alpha_dummy_502;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0523 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb068_alpha_dummy_493) ≠ (nb068_alpha_dummy_497) from
                                    (by
                                      unfold nb068_alpha_dummy_497;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0520)
                                              0)))) (show
                                    (nb068_alpha_dummy_495 f) ≠ (nb068_alpha_dummy_498 f) from
                                    (by
                                      unfold nb068_alpha_dummy_498;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0521 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb068_alpha_dummy_501), (nb068_alpha_dummy_504 f)),
                                  ((nb068_alpha_dummy_500), (nb068_alpha_dummy_503 f)),
                                  ((nb068_alpha_dummy_499), (nb068_alpha_dummy_502 f)),
                                  ((nb068_alpha_dummy_497), (nb068_alpha_dummy_498 f)),
                                  ((nb068_alpha_dummy_493), (nb068_alpha_dummy_495 f)),
                                  ((nb068_alpha_dummy_494), (nb068_alpha_dummy_496 f)),
                                  ((nb068_alpha_dummy_519), (nb068_alpha_dummy_520 f)),
                                  ((nb068_alpha_dummy_517), (nb068_alpha_dummy_518 f)),
                                  ((nb068_alpha_dummy_486), (nb068_alpha_dummy_488 f)),
                                  ((nb068_alpha_dummy_485), (nb068_alpha_dummy_487 f)),
                                  ((nb068_alpha_dummy_515), (nb068_alpha_dummy_516 f)),
                                  ((nb068_alpha_dummy_489), (nb068_alpha_dummy_490 f)),
                                  ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
                                  ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
                                  ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
                                  ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
                                  ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
                                  ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
                                  ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                                  ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003),
                                    (nb068_alpha_dummy_004 x y f))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb068_split_alpha_0125 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb068_alpha_dummy_493) ≠ (nb068_alpha_dummy_497) from (by
                          unfold nb068_alpha_dummy_497;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0520) 0))))
                      (show (nb068_alpha_dummy_495 f) ≠ (nb068_alpha_dummy_498 f) from (by
                          unfold nb068_alpha_dummy_498;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0521 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb068_alpha_dummy_497), (nb068_alpha_dummy_498 f)),
                      ((nb068_alpha_dummy_493), (nb068_alpha_dummy_495 f)),
                      ((nb068_alpha_dummy_494), (nb068_alpha_dummy_496 f)),
                      ((nb068_alpha_dummy_519), (nb068_alpha_dummy_520 f)),
                      ((nb068_alpha_dummy_517), (nb068_alpha_dummy_518 f)),
                      ((nb068_alpha_dummy_486), (nb068_alpha_dummy_488 f)),
                      ((nb068_alpha_dummy_485), (nb068_alpha_dummy_487 f)),
                      ((nb068_alpha_dummy_515), (nb068_alpha_dummy_516 f)),
                      ((nb068_alpha_dummy_489), (nb068_alpha_dummy_490 f)),
                      ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
                      ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
                      ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
                      ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
                      ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
                      ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
                      ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                      ((nb068_alpha_dummy_001), x),
                      ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068_alpha_dummy_493) ≠ (nb068_alpha_dummy_497) from
                      (by
                        unfold nb068_alpha_dummy_497;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0520) 0))))
                    (show (nb068_alpha_dummy_495 f) ≠ (nb068_alpha_dummy_498 f) from (by
                        unfold nb068_alpha_dummy_498;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0521 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068_alpha_dummy_493) ≠ (nb068_alpha_dummy_497) from (by
                          unfold nb068_alpha_dummy_497;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0520) 0))))
                      (show (nb068_alpha_dummy_495 f) ≠ (nb068_alpha_dummy_498 f) from (by
                          unfold nb068_alpha_dummy_498;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0521 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb068_alpha_dummy_497), (nb068_alpha_dummy_498 f)),
                      ((nb068_alpha_dummy_493), (nb068_alpha_dummy_495 f)),
                      ((nb068_alpha_dummy_494), (nb068_alpha_dummy_496 f)),
                      ((nb068_alpha_dummy_519), (nb068_alpha_dummy_520 f)),
                      ((nb068_alpha_dummy_517), (nb068_alpha_dummy_518 f)),
                      ((nb068_alpha_dummy_486), (nb068_alpha_dummy_488 f)),
                      ((nb068_alpha_dummy_485), (nb068_alpha_dummy_487 f)),
                      ((nb068_alpha_dummy_515), (nb068_alpha_dummy_516 f)),
                      ((nb068_alpha_dummy_489), (nb068_alpha_dummy_490 f)),
                      ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
                      ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
                      ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
                      ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
                      ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
                      ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
                      ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                      ((nb068_alpha_dummy_001), x),
                      ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb068_split_alpha_0127 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_515), (nb068_alpha_dummy_516 f)),
        ((nb068_alpha_dummy_489), (nb068_alpha_dummy_490 f)),
        ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
        ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
        ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
        ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
        ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
        ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_515))
          (Class.cab (nb068_alpha_dummy_485)
            (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_328))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_485))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_486))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb068_alpha_dummy_515))
            (Class.cab (nb068_alpha_dummy_485)
              (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_328))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_485))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_486)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_516 f))
          (Class.cab (nb068_alpha_dummy_487 f)
            (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_331 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_488 f)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb068_alpha_dummy_516 f))
            (Class.cab (nb068_alpha_dummy_487 f)
              (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_331 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_488 f)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb068_alpha_dummy_328) ≠ (nb068_alpha_dummy_486) from
                    (by
                      unfold nb068_alpha_dummy_486;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0540) 1))))
                  (show (nb068_alpha_dummy_331 f) ≠ (nb068_alpha_dummy_488 f) from (by
                      unfold nb068_alpha_dummy_488;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0542 f) 1))))
                  (TAlphaVar.there (show (nb068_alpha_dummy_328) ≠ (nb068_alpha_dummy_485) from
                      (by
                        unfold nb068_alpha_dummy_485;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0540) 0))))
                    (show (nb068_alpha_dummy_331 f) ≠ (nb068_alpha_dummy_487 f) from (by
                        unfold nb068_alpha_dummy_487;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0542 f) 0)))) (TAlphaVar.there
                      (show (nb068_alpha_dummy_328) ≠ (nb068_alpha_dummy_515) from (by
                          unfold nb068_alpha_dummy_515;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0544) 0))))
                      (show (nb068_alpha_dummy_331 f) ≠ (nb068_alpha_dummy_516 f) from (by
                          unfold nb068_alpha_dummy_516;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0545 f) 0))))
                      (TAlphaVar.there
                        (show (nb068_alpha_dummy_328) ≠ (nb068_alpha_dummy_489) from (by
                            unfold nb068_alpha_dummy_489;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0541) 0))))
                        (show (nb068_alpha_dummy_331 f) ≠ (nb068_alpha_dummy_490 f) from (by
                            unfold nb068_alpha_dummy_490;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0543 f) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪ ((syn_ccnv
                                  (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))).fv)
                            (by decide)) (freshVar_injective (((syn_ccnv (Class.cv f))).fv ∪
                              ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_329))).fv ∪
                      ((Class.cv (nb068_alpha_dummy_328))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb068_alpha_dummy_332 f))).fv ∪
                      ((Class.cv (nb068_alpha_dummy_331 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068_split_alpha_0126 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068_split_alpha_0126 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb068_alpha_dummy_517), (nb068_alpha_dummy_518 f)),
                          ((nb068_alpha_dummy_486), (nb068_alpha_dummy_488 f)),
                          ((nb068_alpha_dummy_485), (nb068_alpha_dummy_487 f)),
                          ((nb068_alpha_dummy_515), (nb068_alpha_dummy_516 f)),
                          ((nb068_alpha_dummy_489), (nb068_alpha_dummy_490 f)),
                          ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
                          ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
                          ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
                          ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
                          ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
                          ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
                          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                          ((nb068_alpha_dummy_001), x),
                          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068_alpha_dummy_328) ≠ (nb068_alpha_dummy_486) from
                      (by
                        unfold nb068_alpha_dummy_486;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0540) 1))))
                    (show (nb068_alpha_dummy_331 f) ≠ (nb068_alpha_dummy_488 f) from (by
                        unfold nb068_alpha_dummy_488;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0542 f) 1)))) (TAlphaVar.there
                      (show (nb068_alpha_dummy_328) ≠ (nb068_alpha_dummy_485) from (by
                          unfold nb068_alpha_dummy_485;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0540) 0))))
                      (show (nb068_alpha_dummy_331 f) ≠ (nb068_alpha_dummy_487 f) from (by
                          unfold nb068_alpha_dummy_487;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0542 f) 0))))
                      (TAlphaVar.there
                        (show (nb068_alpha_dummy_328) ≠ (nb068_alpha_dummy_515) from (by
                            unfold nb068_alpha_dummy_515;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0544) 0))))
                        (show (nb068_alpha_dummy_331 f) ≠ (nb068_alpha_dummy_516 f) from (by
                            unfold nb068_alpha_dummy_516;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0545 f) 0))))
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_328) ≠ (nb068_alpha_dummy_489) from (by
                              unfold nb068_alpha_dummy_489;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0541) 0))))
                          (show (nb068_alpha_dummy_331 f) ≠ (nb068_alpha_dummy_490 f) from (by
                              unfold nb068_alpha_dummy_490;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0543 f) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪ ((syn_ccnv
                                    (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))).fv)
                              (by decide)) (freshVar_injective (((syn_ccnv (Class.cv f))).fv ∪
                                ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb068_alpha_dummy_329))).fv ∪
                        ((Class.cv (nb068_alpha_dummy_328))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb068_alpha_dummy_332 f))).fv ∪
                        ((Class.cv (nb068_alpha_dummy_331 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068_split_alpha_0126 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068_split_alpha_0126 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb068_alpha_dummy_517), (nb068_alpha_dummy_518 f)),
                            ((nb068_alpha_dummy_486), (nb068_alpha_dummy_488 f)),
                            ((nb068_alpha_dummy_485), (nb068_alpha_dummy_487 f)),
                            ((nb068_alpha_dummy_515), (nb068_alpha_dummy_516 f)),
                            ((nb068_alpha_dummy_489), (nb068_alpha_dummy_490 f)),
                            ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)),
                            ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)),
                            ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)),
                            ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)),
                            ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)),
                            ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)),
                            ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                            ((nb068_alpha_dummy_001), x),
                            ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
