/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4C068C001Part023Stage1

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C068C001Part023`. -/


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
noncomputable def nb068_wpp_refl_0042 (x : Var) (y : Var) (f : Var) :
    TReflOn
      [((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)),
        ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      ((syn_cid)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0042 x y f)

@[expose]
noncomputable def nb068_split_alpha_0033 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)), ((nb068_alpha_dummy_000), f),
        ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_041)) (syn_cnin
            (syn_ccom (Class.cv (nb068_alpha_dummy_000))
              (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))) (syn_cid))) (Wff.neg
          (Wff.classMem (Class.cv (nb068_alpha_dummy_041)) (syn_cnin
              (syn_ccom (Class.cv (nb068_alpha_dummy_000))
                (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))) (syn_cid)))))
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_042 f))
          (syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))) (Wff.neg
          (Wff.classMem (Class.cv (nb068_alpha_dummy_042 f))
            (syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (Ne.symm
                              (show (nb068_alpha_dummy_046) ≠ (nb068_alpha_dummy_051) from (by
                                  unfold nb068_alpha_dummy_051;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0044) 0)))))
                            (Ne.symm (show (nb068_alpha_dummy_049 f) ≠ (nb068_alpha_dummy_052 f)
                                from (by
                                  unfold nb068_alpha_dummy_052;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0045 f) 0)))))
                            (TAlphaVar.there (Ne.symm
                                (show (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_051) from (by
                                    unfold nb068_alpha_dummy_051;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0042) 0)))))
                              (Ne.symm (show
                                  (nb068_alpha_dummy_048 f) ≠ (nb068_alpha_dummy_052 f) from (by
                                    unfold nb068_alpha_dummy_052;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0043 f)
                                            0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_054) from (by
          unfold nb068_alpha_dummy_054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0046)
                  1)))) (show (nb068_alpha_dummy_048 f) ≠ (nb068_alpha_dummy_056 f) from (by
          unfold nb068_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0048 f)
                  1)))) (TAlphaVar.there (show (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_053)
        from (by
          unfold nb068_alpha_dummy_053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0046)
                  0)))) (show (nb068_alpha_dummy_048 f) ≠ (nb068_alpha_dummy_055 f) from (by
          unfold nb068_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0048
                    f)
                  0)))) (TAlphaVar.there (show (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_059)
        from (by
          unfold nb068_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0050)
                  0)))) (show (nb068_alpha_dummy_048 f) ≠ (nb068_alpha_dummy_060 f) from (by
          unfold nb068_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0051
                    f)
                  0)))) (TAlphaVar.there (show (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_057)
        from (by
          unfold
            nb068_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0047)
                  0)))) (show (nb068_alpha_dummy_048 f) ≠ (nb068_alpha_dummy_058 f) from (by
          unfold
            nb068_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0049
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb068_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv)
        (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_045))).fv ∪
        ((Class.cv (nb068_alpha_dummy_046))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb068_alpha_dummy_048 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_049 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all
        (nb068_split_alpha_0006 x y f))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_054) from (by
          unfold nb068_alpha_dummy_054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0046)
                  1)))) (show (nb068_alpha_dummy_048 f) ≠ (nb068_alpha_dummy_056 f) from (by
          unfold nb068_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0048 f)
                  1)))) (TAlphaVar.there (show (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_053)
        from (by
          unfold nb068_alpha_dummy_053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0046)
                  0)))) (show (nb068_alpha_dummy_048 f) ≠ (nb068_alpha_dummy_055 f) from (by
          unfold nb068_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0048
                    f)
                  0)))) (TAlphaVar.there (show (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_059)
        from (by
          unfold nb068_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0050)
                  0)))) (show (nb068_alpha_dummy_048 f) ≠ (nb068_alpha_dummy_060 f) from (by
          unfold nb068_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0051
                    f)
                  0)))) (TAlphaVar.there (show (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_057)
        from (by
          unfold
            nb068_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0047)
                  0)))) (show (nb068_alpha_dummy_048 f) ≠ (nb068_alpha_dummy_058 f) from (by
          unfold
            nb068_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0049
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb068_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv)
        (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_045))).fv ∪
        ((Class.cv (nb068_alpha_dummy_046))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb068_alpha_dummy_048 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_049 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all
        (nb068_split_alpha_0006 x y f)))))))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.neg (nb068_split_alpha_0009 x y f)))))))))
                      (TAlphaWff.ex (TAlphaWff.neg (nb068_split_alpha_0032 x y f))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)),
                  ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)),
                  ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                  ((nb068_alpha_dummy_001), x),
                  ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                (syn_cid) (nb068_wpp_refl_0042 x y f))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
                            (TAlphaVar.there (Ne.symm
                                (show (nb068_alpha_dummy_046) ≠ (nb068_alpha_dummy_051) from (by
                                    unfold nb068_alpha_dummy_051;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0044) 0)))))
                              (Ne.symm (show
                                  (nb068_alpha_dummy_049 f) ≠ (nb068_alpha_dummy_052 f) from (by
                                    unfold nb068_alpha_dummy_052;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0045 f)
                                            0))))) (TAlphaVar.there (Ne.symm
                                  (show (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_051) from
                                    (by
                                      unfold nb068_alpha_dummy_051;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0042)
                                              0))))) (Ne.symm (show
                                    (nb068_alpha_dummy_048 f) ≠ (nb068_alpha_dummy_052 f) from
                                    (by
                                      unfold nb068_alpha_dummy_052;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0043 f)
                                              0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_054) from (by
          unfold nb068_alpha_dummy_054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0046)
                  1)))) (show (nb068_alpha_dummy_048 f) ≠ (nb068_alpha_dummy_056 f) from (by
          unfold nb068_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0048
                    f)
                  1)))) (TAlphaVar.there (show (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_053)
        from (by
          unfold nb068_alpha_dummy_053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0046)
                  0)))) (show (nb068_alpha_dummy_048 f) ≠ (nb068_alpha_dummy_055 f) from (by
          unfold nb068_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0048
                    f)
                  0)))) (TAlphaVar.there (show (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_059)
        from (by
          unfold
            nb068_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0050)
                  0)))) (show (nb068_alpha_dummy_048 f) ≠ (nb068_alpha_dummy_060 f) from (by
          unfold
            nb068_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0051
                    f)
                  0)))) (TAlphaVar.there (show (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_057)
        from (by
          unfold
            nb068_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0047)
                  0)))) (show (nb068_alpha_dummy_048 f) ≠ (nb068_alpha_dummy_058 f) from (by
          unfold
            nb068_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0049
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb068_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv)
        (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_045))).fv ∪
        ((Class.cv (nb068_alpha_dummy_046))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb068_alpha_dummy_048 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_049 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all
        (nb068_split_alpha_0006 x y f))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_054) from (by
          unfold nb068_alpha_dummy_054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0046)
                  1)))) (show (nb068_alpha_dummy_048 f) ≠ (nb068_alpha_dummy_056 f) from (by
          unfold nb068_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0048
                    f)
                  1)))) (TAlphaVar.there (show (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_053)
        from (by
          unfold nb068_alpha_dummy_053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0046)
                  0)))) (show (nb068_alpha_dummy_048 f) ≠ (nb068_alpha_dummy_055 f) from (by
          unfold nb068_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0048
                    f)
                  0)))) (TAlphaVar.there (show (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_059)
        from (by
          unfold
            nb068_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0050)
                  0)))) (show (nb068_alpha_dummy_048 f) ≠ (nb068_alpha_dummy_060 f) from (by
          unfold
            nb068_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0051
                    f)
                  0)))) (TAlphaVar.there (show (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_057)
        from (by
          unfold
            nb068_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0047)
                  0)))) (show (nb068_alpha_dummy_048 f) ≠ (nb068_alpha_dummy_058 f) from (by
          unfold
            nb068_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0049
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb068_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv)
        (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_045))).fv ∪
        ((Class.cv (nb068_alpha_dummy_046))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb068_alpha_dummy_048 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_049 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all
        (nb068_split_alpha_0006 x y f))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg (TAlphaWff.neg
                                        (nb068_split_alpha_0009 x y f)))))))))
                        (TAlphaWff.ex (TAlphaWff.neg (nb068_split_alpha_0032 x y f))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_reflOn
                  [((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)),
                    ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)),
                    ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                    ((nb068_alpha_dummy_001), x),
                    ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                  (syn_cid) (nb068_wpp_refl_0042 x y f)))))))))

@[expose]
noncomputable def nb068_split_alpha_0034 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_069), (nb068_alpha_dummy_072 f)),
        ((nb068_alpha_dummy_068), (nb068_alpha_dummy_071 f)),
        ((nb068_alpha_dummy_067), (nb068_alpha_dummy_070 f)),
        ((nb068_alpha_dummy_065), (nb068_alpha_dummy_066 f)),
        ((nb068_alpha_dummy_061), (nb068_alpha_dummy_063 f)),
        ((nb068_alpha_dummy_062), (nb068_alpha_dummy_064 f)),
        ((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)),
        ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)),
        ((nb068_alpha_dummy_059), (nb068_alpha_dummy_060 f)),
        ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)),
        ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
        ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
        ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb068_alpha_dummy_068)) (Class.cv (nb068_alpha_dummy_069)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_067))
            (syn_cun (Class.cv (nb068_alpha_dummy_068)) (Class.cv (nb068_alpha_dummy_069))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_071 f))
            (Class.cv (nb068_alpha_dummy_072 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_070 f))
            (syn_cun (Class.cv (nb068_alpha_dummy_071 f))
              (Class.cv (nb068_alpha_dummy_072 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_068) ≠ (nb068_alpha_dummy_075) from (by
                              unfold nb068_alpha_dummy_075;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0060) 0))))
                          (show (nb068_alpha_dummy_071 f) ≠ (nb068_alpha_dummy_076 f) from (by
                              unfold nb068_alpha_dummy_076;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0061 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_068) ≠ (nb068_alpha_dummy_073) from (by
                                unfold nb068_alpha_dummy_073;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0058) 0))))
                            (show (nb068_alpha_dummy_071 f) ≠ (nb068_alpha_dummy_074 f) from (by
                                unfold nb068_alpha_dummy_074;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0059 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_069) ≠ (nb068_alpha_dummy_075) from (by
                              unfold nb068_alpha_dummy_075;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0064) 0))))
                          (show (nb068_alpha_dummy_072 f) ≠ (nb068_alpha_dummy_076 f) from (by
                              unfold nb068_alpha_dummy_076;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0065 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_069) ≠ (nb068_alpha_dummy_073) from (by
                                unfold nb068_alpha_dummy_073;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0062) 0))))
                            (show (nb068_alpha_dummy_072 f) ≠ (nb068_alpha_dummy_074 f) from (by
                                unfold nb068_alpha_dummy_074;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0063 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_068) ≠ (nb068_alpha_dummy_075) from (by
                              unfold nb068_alpha_dummy_075;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0060) 0))))
                          (show (nb068_alpha_dummy_071 f) ≠ (nb068_alpha_dummy_076 f) from (by
                              unfold nb068_alpha_dummy_076;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0061 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_068) ≠ (nb068_alpha_dummy_073) from (by
                                unfold nb068_alpha_dummy_073;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0058) 0))))
                            (show (nb068_alpha_dummy_071 f) ≠ (nb068_alpha_dummy_074 f) from (by
                                unfold nb068_alpha_dummy_074;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0059 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_069) ≠ (nb068_alpha_dummy_075) from (by
                              unfold nb068_alpha_dummy_075;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0064) 0))))
                          (show (nb068_alpha_dummy_072 f) ≠ (nb068_alpha_dummy_076 f) from (by
                              unfold nb068_alpha_dummy_076;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0065 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_069) ≠ (nb068_alpha_dummy_073) from (by
                                unfold nb068_alpha_dummy_073;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0062) 0))))
                            (show (nb068_alpha_dummy_072 f) ≠ (nb068_alpha_dummy_074 f) from (by
                                unfold nb068_alpha_dummy_074;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0063 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb068_alpha_dummy_069), (nb068_alpha_dummy_072 f)),
          ((nb068_alpha_dummy_068), (nb068_alpha_dummy_071 f)),
          ((nb068_alpha_dummy_067), (nb068_alpha_dummy_070 f)),
          ((nb068_alpha_dummy_065), (nb068_alpha_dummy_066 f)),
          ((nb068_alpha_dummy_061), (nb068_alpha_dummy_063 f)),
          ((nb068_alpha_dummy_062), (nb068_alpha_dummy_064 f)),
          ((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)),
          ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)),
          ((nb068_alpha_dummy_059), (nb068_alpha_dummy_060 f)),
          ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)),
          ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
          ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
          ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
          ((nb068_alpha_dummy_001), x),
          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_068) ≠ (nb068_alpha_dummy_079) from (by
                                unfold nb068_alpha_dummy_079;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0068) 0))))
                            (show (nb068_alpha_dummy_071 f) ≠ (nb068_alpha_dummy_080 f) from (by
                                unfold nb068_alpha_dummy_080;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0069 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_068) ≠ (nb068_alpha_dummy_077) from (by
                                  unfold nb068_alpha_dummy_077;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0066) 0))))
                              (show (nb068_alpha_dummy_071 f) ≠ (nb068_alpha_dummy_078 f) from
                                (by
                                  unfold nb068_alpha_dummy_078;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0067 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_068) ≠ (nb068_alpha_dummy_079) from (by
                                unfold nb068_alpha_dummy_079;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0068) 0))))
                            (show (nb068_alpha_dummy_071 f) ≠ (nb068_alpha_dummy_080 f) from (by
                                unfold nb068_alpha_dummy_080;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0069 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_068) ≠ (nb068_alpha_dummy_077) from (by
                                  unfold nb068_alpha_dummy_077;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0066) 0))))
                              (show (nb068_alpha_dummy_071 f) ≠ (nb068_alpha_dummy_078 f) from
                                (by
                                  unfold nb068_alpha_dummy_078;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0067 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_069) ≠ (nb068_alpha_dummy_081) from (by
                                unfold nb068_alpha_dummy_081;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0072) 0))))
                            (show (nb068_alpha_dummy_072 f) ≠ (nb068_alpha_dummy_082 f) from (by
                                unfold nb068_alpha_dummy_082;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0073 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_069) ≠ (nb068_alpha_dummy_077) from (by
                                  unfold nb068_alpha_dummy_077;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0070) 0))))
                              (show (nb068_alpha_dummy_072 f) ≠ (nb068_alpha_dummy_078 f) from
                                (by
                                  unfold nb068_alpha_dummy_078;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0071 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_069) ≠ (nb068_alpha_dummy_081) from (by
                                unfold nb068_alpha_dummy_081;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0072) 0))))
                            (show (nb068_alpha_dummy_072 f) ≠ (nb068_alpha_dummy_082 f) from (by
                                unfold nb068_alpha_dummy_082;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0073 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_069) ≠ (nb068_alpha_dummy_077) from (by
                                  unfold nb068_alpha_dummy_077;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0070) 0))))
                              (show (nb068_alpha_dummy_072 f) ≠ (nb068_alpha_dummy_078 f) from
                                (by
                                  unfold nb068_alpha_dummy_078;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0071 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb068_split_alpha_0035 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)),
        ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)),
        ((nb068_alpha_dummy_059), (nb068_alpha_dummy_060 f)),
        ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)),
        ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
        ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
        ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.classEq (Class.cv (nb068_alpha_dummy_053))
        (syn_cphi (Class.cv (nb068_alpha_dummy_054))))
      (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f))
        (syn_cphi (Class.cv (nb068_alpha_dummy_056 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb068_alpha_dummy_045))).fv ∪ ((Class.cv (nb068_alpha_dummy_046))).fv)
          (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪
            ((Class.cv (nb068_alpha_dummy_049 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (show (nb068_alpha_dummy_054) ≠ (nb068_alpha_dummy_061) from (by
                    unfold nb068_alpha_dummy_061;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0052) 0))))
                (show (nb068_alpha_dummy_056 f) ≠ (nb068_alpha_dummy_063 f) from (by
                    unfold nb068_alpha_dummy_063;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0053 f) 0))))
                (TAlphaVar.there (show (nb068_alpha_dummy_054) ≠ (nb068_alpha_dummy_062) from
                    (by
                      unfold nb068_alpha_dummy_062;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0052) 1))))
                  (show (nb068_alpha_dummy_056 f) ≠ (nb068_alpha_dummy_064 f) from (by
                      unfold nb068_alpha_dummy_064;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0053 f) 1))))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb068_alpha_dummy_054))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb068_alpha_dummy_056 f))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb068_alpha_dummy_061) ≠ (nb068_alpha_dummy_068) from
                                    (by
                                      unfold nb068_alpha_dummy_068;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0056)
                                              1)))) (show
                                    (nb068_alpha_dummy_063 f) ≠ (nb068_alpha_dummy_071 f) from
                                    (by
                                      unfold nb068_alpha_dummy_071;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0057 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb068_alpha_dummy_061) ≠ (nb068_alpha_dummy_067) from (by
                                        unfold nb068_alpha_dummy_067;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0056)
                                                0)))) (show (nb068_alpha_dummy_063 f) ≠
                                        (nb068_alpha_dummy_070 f) from (by
                                        unfold nb068_alpha_dummy_070;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0057 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068_alpha_dummy_061) ≠ (nb068_alpha_dummy_065) from
                                        (by
                                          unfold nb068_alpha_dummy_065;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0054)
                                                  0)))) (show (nb068_alpha_dummy_063 f) ≠
        (nb068_alpha_dummy_066 f) from (by
                                          unfold nb068_alpha_dummy_066;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0055 f) 0))))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.refl_of_closed
                                    [((nb068_alpha_dummy_069), (nb068_alpha_dummy_072 f)),
                                      ((nb068_alpha_dummy_068), (nb068_alpha_dummy_071 f)),
                                      ((nb068_alpha_dummy_067), (nb068_alpha_dummy_070 f)),
                                      ((nb068_alpha_dummy_065), (nb068_alpha_dummy_066 f)),
                                      ((nb068_alpha_dummy_061), (nb068_alpha_dummy_063 f)),
                                      ((nb068_alpha_dummy_062), (nb068_alpha_dummy_064 f)),
                                      ((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)),
                                      ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)),
                                      ((nb068_alpha_dummy_059), (nb068_alpha_dummy_060 f)),
                                      ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)),
                                      ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
                                      ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
                                      ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
                                      ((nb068_alpha_dummy_000), f),
                                      ((nb068_alpha_dummy_002), y),
                                      ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003),
                                        (nb068_alpha_dummy_004 x y f))]
                                    (syn_c1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb068_split_alpha_0034 x y f))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (show (nb068_alpha_dummy_061) ≠ (nb068_alpha_dummy_065) from (by
                              unfold nb068_alpha_dummy_065;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0054) 0))))
                          (show (nb068_alpha_dummy_063 f) ≠ (nb068_alpha_dummy_066 f) from (by
                              unfold nb068_alpha_dummy_066;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0055 f) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb068_alpha_dummy_065), (nb068_alpha_dummy_066 f)),
                          ((nb068_alpha_dummy_061), (nb068_alpha_dummy_063 f)),
                          ((nb068_alpha_dummy_062), (nb068_alpha_dummy_064 f)),
                          ((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)),
                          ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)),
                          ((nb068_alpha_dummy_059), (nb068_alpha_dummy_060 f)),
                          ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)),
                          ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
                          ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
                          ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
                          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                          ((nb068_alpha_dummy_001), x),
                          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb068_alpha_dummy_061) ≠ (nb068_alpha_dummy_065) from (by
                            unfold nb068_alpha_dummy_065;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0054) 0))))
                        (show (nb068_alpha_dummy_063 f) ≠ (nb068_alpha_dummy_066 f) from (by
                            unfold nb068_alpha_dummy_066;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0055 f) 0))))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (show (nb068_alpha_dummy_061) ≠ (nb068_alpha_dummy_065) from (by
                              unfold nb068_alpha_dummy_065;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0054) 0))))
                          (show (nb068_alpha_dummy_063 f) ≠ (nb068_alpha_dummy_066 f) from (by
                              unfold nb068_alpha_dummy_066;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0055 f) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb068_alpha_dummy_065), (nb068_alpha_dummy_066 f)),
                          ((nb068_alpha_dummy_061), (nb068_alpha_dummy_063 f)),
                          ((nb068_alpha_dummy_062), (nb068_alpha_dummy_064 f)),
                          ((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)),
                          ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)),
                          ((nb068_alpha_dummy_059), (nb068_alpha_dummy_060 f)),
                          ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)),
                          ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
                          ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
                          ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
                          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                          ((nb068_alpha_dummy_001), x),
                          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part024`. -/


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
noncomputable def nb068_split_alpha_0036 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_069), (nb068_alpha_dummy_072 f)),
        ((nb068_alpha_dummy_068), (nb068_alpha_dummy_071 f)),
        ((nb068_alpha_dummy_067), (nb068_alpha_dummy_070 f)),
        ((nb068_alpha_dummy_065), (nb068_alpha_dummy_066 f)),
        ((nb068_alpha_dummy_061), (nb068_alpha_dummy_063 f)),
        ((nb068_alpha_dummy_062), (nb068_alpha_dummy_064 f)),
        ((nb068_alpha_dummy_087), (nb068_alpha_dummy_088 f)),
        ((nb068_alpha_dummy_085), (nb068_alpha_dummy_086 f)),
        ((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)),
        ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)),
        ((nb068_alpha_dummy_083), (nb068_alpha_dummy_084 f)),
        ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)),
        ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
        ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
        ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb068_alpha_dummy_068)) (Class.cv (nb068_alpha_dummy_069)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_067))
            (syn_cun (Class.cv (nb068_alpha_dummy_068)) (Class.cv (nb068_alpha_dummy_069))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_071 f))
            (Class.cv (nb068_alpha_dummy_072 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_070 f))
            (syn_cun (Class.cv (nb068_alpha_dummy_071 f))
              (Class.cv (nb068_alpha_dummy_072 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_068) ≠ (nb068_alpha_dummy_075) from (by
                              unfold nb068_alpha_dummy_075;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0060) 0))))
                          (show (nb068_alpha_dummy_071 f) ≠ (nb068_alpha_dummy_076 f) from (by
                              unfold nb068_alpha_dummy_076;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0061 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_068) ≠ (nb068_alpha_dummy_073) from (by
                                unfold nb068_alpha_dummy_073;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0058) 0))))
                            (show (nb068_alpha_dummy_071 f) ≠ (nb068_alpha_dummy_074 f) from (by
                                unfold nb068_alpha_dummy_074;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0059 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_069) ≠ (nb068_alpha_dummy_075) from (by
                              unfold nb068_alpha_dummy_075;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0064) 0))))
                          (show (nb068_alpha_dummy_072 f) ≠ (nb068_alpha_dummy_076 f) from (by
                              unfold nb068_alpha_dummy_076;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0065 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_069) ≠ (nb068_alpha_dummy_073) from (by
                                unfold nb068_alpha_dummy_073;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0062) 0))))
                            (show (nb068_alpha_dummy_072 f) ≠ (nb068_alpha_dummy_074 f) from (by
                                unfold nb068_alpha_dummy_074;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0063 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_068) ≠ (nb068_alpha_dummy_075) from (by
                              unfold nb068_alpha_dummy_075;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0060) 0))))
                          (show (nb068_alpha_dummy_071 f) ≠ (nb068_alpha_dummy_076 f) from (by
                              unfold nb068_alpha_dummy_076;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0061 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_068) ≠ (nb068_alpha_dummy_073) from (by
                                unfold nb068_alpha_dummy_073;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0058) 0))))
                            (show (nb068_alpha_dummy_071 f) ≠ (nb068_alpha_dummy_074 f) from (by
                                unfold nb068_alpha_dummy_074;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0059 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_069) ≠ (nb068_alpha_dummy_075) from (by
                              unfold nb068_alpha_dummy_075;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0064) 0))))
                          (show (nb068_alpha_dummy_072 f) ≠ (nb068_alpha_dummy_076 f) from (by
                              unfold nb068_alpha_dummy_076;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0065 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_069) ≠ (nb068_alpha_dummy_073) from (by
                                unfold nb068_alpha_dummy_073;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0062) 0))))
                            (show (nb068_alpha_dummy_072 f) ≠ (nb068_alpha_dummy_074 f) from (by
                                unfold nb068_alpha_dummy_074;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0063 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb068_alpha_dummy_069), (nb068_alpha_dummy_072 f)),
          ((nb068_alpha_dummy_068), (nb068_alpha_dummy_071 f)),
          ((nb068_alpha_dummy_067), (nb068_alpha_dummy_070 f)),
          ((nb068_alpha_dummy_065), (nb068_alpha_dummy_066 f)),
          ((nb068_alpha_dummy_061), (nb068_alpha_dummy_063 f)),
          ((nb068_alpha_dummy_062), (nb068_alpha_dummy_064 f)),
          ((nb068_alpha_dummy_087), (nb068_alpha_dummy_088 f)),
          ((nb068_alpha_dummy_085), (nb068_alpha_dummy_086 f)),
          ((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)),
          ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)),
          ((nb068_alpha_dummy_083), (nb068_alpha_dummy_084 f)),
          ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)),
          ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
          ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
          ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
          ((nb068_alpha_dummy_001), x),
          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_068) ≠ (nb068_alpha_dummy_079) from (by
                                unfold nb068_alpha_dummy_079;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0068) 0))))
                            (show (nb068_alpha_dummy_071 f) ≠ (nb068_alpha_dummy_080 f) from (by
                                unfold nb068_alpha_dummy_080;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0069 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_068) ≠ (nb068_alpha_dummy_077) from (by
                                  unfold nb068_alpha_dummy_077;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0066) 0))))
                              (show (nb068_alpha_dummy_071 f) ≠ (nb068_alpha_dummy_078 f) from
                                (by
                                  unfold nb068_alpha_dummy_078;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0067 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_068) ≠ (nb068_alpha_dummy_079) from (by
                                unfold nb068_alpha_dummy_079;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0068) 0))))
                            (show (nb068_alpha_dummy_071 f) ≠ (nb068_alpha_dummy_080 f) from (by
                                unfold nb068_alpha_dummy_080;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0069 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_068) ≠ (nb068_alpha_dummy_077) from (by
                                  unfold nb068_alpha_dummy_077;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0066) 0))))
                              (show (nb068_alpha_dummy_071 f) ≠ (nb068_alpha_dummy_078 f) from
                                (by
                                  unfold nb068_alpha_dummy_078;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0067 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_069) ≠ (nb068_alpha_dummy_081) from (by
                                unfold nb068_alpha_dummy_081;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0072) 0))))
                            (show (nb068_alpha_dummy_072 f) ≠ (nb068_alpha_dummy_082 f) from (by
                                unfold nb068_alpha_dummy_082;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0073 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_069) ≠ (nb068_alpha_dummy_077) from (by
                                  unfold nb068_alpha_dummy_077;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0070) 0))))
                              (show (nb068_alpha_dummy_072 f) ≠ (nb068_alpha_dummy_078 f) from
                                (by
                                  unfold nb068_alpha_dummy_078;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0071 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_069) ≠ (nb068_alpha_dummy_081) from (by
                                unfold nb068_alpha_dummy_081;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0072) 0))))
                            (show (nb068_alpha_dummy_072 f) ≠ (nb068_alpha_dummy_082 f) from (by
                                unfold nb068_alpha_dummy_082;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0073 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_069) ≠ (nb068_alpha_dummy_077) from (by
                                  unfold nb068_alpha_dummy_077;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0070) 0))))
                              (show (nb068_alpha_dummy_072 f) ≠ (nb068_alpha_dummy_078 f) from
                                (by
                                  unfold nb068_alpha_dummy_078;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0071 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb068_split_alpha_0037 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_061), (nb068_alpha_dummy_063 f)),
        ((nb068_alpha_dummy_062), (nb068_alpha_dummy_064 f)),
        ((nb068_alpha_dummy_087), (nb068_alpha_dummy_088 f)),
        ((nb068_alpha_dummy_085), (nb068_alpha_dummy_086 f)),
        ((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)),
        ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)),
        ((nb068_alpha_dummy_083), (nb068_alpha_dummy_084 f)),
        ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)),
        ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
        ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
        ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_061))
          (Class.cv (nb068_alpha_dummy_054))) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_062))
            (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_061)) (syn_cnnc))
              (syn_cplc (Class.cv (nb068_alpha_dummy_061)) (syn_c1c))
              (Class.cv (nb068_alpha_dummy_061))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_063 f))
          (Class.cv (nb068_alpha_dummy_056 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_064 f))
            (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_063 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb068_alpha_dummy_063 f)) (syn_c1c))
              (Class.cv (nb068_alpha_dummy_063 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068_alpha_dummy_054) ≠ (nb068_alpha_dummy_061) from (by
              unfold nb068_alpha_dummy_061;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0052) 0))))
          (show (nb068_alpha_dummy_056 f) ≠ (nb068_alpha_dummy_063 f) from (by
              unfold nb068_alpha_dummy_063;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0053 f) 0))))
          (TAlphaVar.there (show (nb068_alpha_dummy_054) ≠ (nb068_alpha_dummy_062) from (by
                unfold nb068_alpha_dummy_062;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0052) 1))))
            (show (nb068_alpha_dummy_056 f) ≠ (nb068_alpha_dummy_064 f) from (by
                unfold nb068_alpha_dummy_064;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0053 f) 1))))
            (TAlphaVar.there (show (nb068_alpha_dummy_054) ≠ (nb068_alpha_dummy_087) from (by
                  unfold nb068_alpha_dummy_087;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0082) 0))))
              (show (nb068_alpha_dummy_056 f) ≠ (nb068_alpha_dummy_088 f) from (by
                  unfold nb068_alpha_dummy_088;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0083 f) 0))))
              (TAlphaVar.there (show (nb068_alpha_dummy_054) ≠ (nb068_alpha_dummy_085) from (by
                    unfold nb068_alpha_dummy_085;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0080) 0))))
                (show (nb068_alpha_dummy_056 f) ≠ (nb068_alpha_dummy_086 f) from (by
                    unfold nb068_alpha_dummy_086;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0081 f) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_054))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_056 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068_alpha_dummy_061) ≠ (nb068_alpha_dummy_068) from (by
                                  unfold nb068_alpha_dummy_068;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0056) 1))))
                              (show (nb068_alpha_dummy_063 f) ≠ (nb068_alpha_dummy_071 f) from
                                (by
                                  unfold nb068_alpha_dummy_071;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0057 f) 1))))
                              (TAlphaVar.there
                                (show (nb068_alpha_dummy_061) ≠ (nb068_alpha_dummy_067) from (by
                                    unfold nb068_alpha_dummy_067;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0056) 0)))) (show
                                  (nb068_alpha_dummy_063 f) ≠ (nb068_alpha_dummy_070 f) from (by
                                    unfold nb068_alpha_dummy_070;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0057 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb068_alpha_dummy_061) ≠ (nb068_alpha_dummy_065) from
                                    (by
                                      unfold nb068_alpha_dummy_065;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0054)
                                              0)))) (show
                                    (nb068_alpha_dummy_063 f) ≠ (nb068_alpha_dummy_066 f) from
                                    (by
                                      unfold nb068_alpha_dummy_066;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0055 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb068_alpha_dummy_069), (nb068_alpha_dummy_072 f)),
                                  ((nb068_alpha_dummy_068), (nb068_alpha_dummy_071 f)),
                                  ((nb068_alpha_dummy_067), (nb068_alpha_dummy_070 f)),
                                  ((nb068_alpha_dummy_065), (nb068_alpha_dummy_066 f)),
                                  ((nb068_alpha_dummy_061), (nb068_alpha_dummy_063 f)),
                                  ((nb068_alpha_dummy_062), (nb068_alpha_dummy_064 f)),
                                  ((nb068_alpha_dummy_087), (nb068_alpha_dummy_088 f)),
                                  ((nb068_alpha_dummy_085), (nb068_alpha_dummy_086 f)),
                                  ((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)),
                                  ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)),
                                  ((nb068_alpha_dummy_083), (nb068_alpha_dummy_084 f)),
                                  ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)),
                                  ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
                                  ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
                                  ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
                                  ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                                  ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003),
                                    (nb068_alpha_dummy_004 x y f))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb068_split_alpha_0036 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb068_alpha_dummy_061) ≠ (nb068_alpha_dummy_065) from (by
                          unfold nb068_alpha_dummy_065;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0054) 0))))
                      (show (nb068_alpha_dummy_063 f) ≠ (nb068_alpha_dummy_066 f) from (by
                          unfold nb068_alpha_dummy_066;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0055 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb068_alpha_dummy_065), (nb068_alpha_dummy_066 f)),
                      ((nb068_alpha_dummy_061), (nb068_alpha_dummy_063 f)),
                      ((nb068_alpha_dummy_062), (nb068_alpha_dummy_064 f)),
                      ((nb068_alpha_dummy_087), (nb068_alpha_dummy_088 f)),
                      ((nb068_alpha_dummy_085), (nb068_alpha_dummy_086 f)),
                      ((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)),
                      ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)),
                      ((nb068_alpha_dummy_083), (nb068_alpha_dummy_084 f)),
                      ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)),
                      ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
                      ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
                      ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
                      ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                      ((nb068_alpha_dummy_001), x),
                      ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068_alpha_dummy_061) ≠ (nb068_alpha_dummy_065) from
                      (by
                        unfold nb068_alpha_dummy_065;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0054) 0))))
                    (show (nb068_alpha_dummy_063 f) ≠ (nb068_alpha_dummy_066 f) from (by
                        unfold nb068_alpha_dummy_066;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0055 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068_alpha_dummy_061) ≠ (nb068_alpha_dummy_065) from (by
                          unfold nb068_alpha_dummy_065;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0054) 0))))
                      (show (nb068_alpha_dummy_063 f) ≠ (nb068_alpha_dummy_066 f) from (by
                          unfold nb068_alpha_dummy_066;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0055 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb068_alpha_dummy_065), (nb068_alpha_dummy_066 f)),
                      ((nb068_alpha_dummy_061), (nb068_alpha_dummy_063 f)),
                      ((nb068_alpha_dummy_062), (nb068_alpha_dummy_064 f)),
                      ((nb068_alpha_dummy_087), (nb068_alpha_dummy_088 f)),
                      ((nb068_alpha_dummy_085), (nb068_alpha_dummy_086 f)),
                      ((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)),
                      ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)),
                      ((nb068_alpha_dummy_083), (nb068_alpha_dummy_084 f)),
                      ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)),
                      ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
                      ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
                      ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
                      ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                      ((nb068_alpha_dummy_001), x),
                      ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb068_split_alpha_0038 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_083), (nb068_alpha_dummy_084 f)),
        ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)),
        ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
        ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
        ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_083))
          (Class.cab (nb068_alpha_dummy_053)
            (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_046))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_053))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_054))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb068_alpha_dummy_083))
            (Class.cab (nb068_alpha_dummy_053)
              (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_046))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_053))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_054)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_084 f))
          (Class.cab (nb068_alpha_dummy_055 f)
            (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_049 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_056 f)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb068_alpha_dummy_084 f))
            (Class.cab (nb068_alpha_dummy_055 f)
              (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_049 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_056 f)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb068_alpha_dummy_046) ≠ (nb068_alpha_dummy_054) from
                    (by
                      unfold nb068_alpha_dummy_054;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0074) 1))))
                  (show (nb068_alpha_dummy_049 f) ≠ (nb068_alpha_dummy_056 f) from (by
                      unfold nb068_alpha_dummy_056;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0076 f) 1))))
                  (TAlphaVar.there (show (nb068_alpha_dummy_046) ≠ (nb068_alpha_dummy_053) from
                      (by
                        unfold nb068_alpha_dummy_053;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0074) 0))))
                    (show (nb068_alpha_dummy_049 f) ≠ (nb068_alpha_dummy_055 f) from (by
                        unfold nb068_alpha_dummy_055;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0076 f) 0)))) (TAlphaVar.there
                      (show (nb068_alpha_dummy_046) ≠ (nb068_alpha_dummy_083) from (by
                          unfold nb068_alpha_dummy_083;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0078) 0))))
                      (show (nb068_alpha_dummy_049 f) ≠ (nb068_alpha_dummy_084 f) from (by
                          unfold nb068_alpha_dummy_084;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0079 f) 0))))
                      (TAlphaVar.there
                        (show (nb068_alpha_dummy_046) ≠ (nb068_alpha_dummy_057) from (by
                            unfold nb068_alpha_dummy_057;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0075) 0))))
                        (show (nb068_alpha_dummy_049 f) ≠ (nb068_alpha_dummy_058 f) from (by
                            unfold nb068_alpha_dummy_058;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0077 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_045))).fv ∪
                      ((Class.cv (nb068_alpha_dummy_046))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪
                      ((Class.cv (nb068_alpha_dummy_049 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068_split_alpha_0037 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068_split_alpha_0037 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb068_alpha_dummy_085), (nb068_alpha_dummy_086 f)),
                          ((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)),
                          ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)),
                          ((nb068_alpha_dummy_083), (nb068_alpha_dummy_084 f)),
                          ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)),
                          ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
                          ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
                          ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
                          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                          ((nb068_alpha_dummy_001), x),
                          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068_alpha_dummy_046) ≠ (nb068_alpha_dummy_054) from
                      (by
                        unfold nb068_alpha_dummy_054;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0074) 1))))
                    (show (nb068_alpha_dummy_049 f) ≠ (nb068_alpha_dummy_056 f) from (by
                        unfold nb068_alpha_dummy_056;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0076 f) 1)))) (TAlphaVar.there
                      (show (nb068_alpha_dummy_046) ≠ (nb068_alpha_dummy_053) from (by
                          unfold nb068_alpha_dummy_053;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0074) 0))))
                      (show (nb068_alpha_dummy_049 f) ≠ (nb068_alpha_dummy_055 f) from (by
                          unfold nb068_alpha_dummy_055;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0076 f) 0))))
                      (TAlphaVar.there
                        (show (nb068_alpha_dummy_046) ≠ (nb068_alpha_dummy_083) from (by
                            unfold nb068_alpha_dummy_083;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0078) 0))))
                        (show (nb068_alpha_dummy_049 f) ≠ (nb068_alpha_dummy_084 f) from (by
                            unfold nb068_alpha_dummy_084;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0079 f) 0))))
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_046) ≠ (nb068_alpha_dummy_057) from (by
                              unfold nb068_alpha_dummy_057;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0075) 0))))
                          (show (nb068_alpha_dummy_049 f) ≠ (nb068_alpha_dummy_058 f) from (by
                              unfold nb068_alpha_dummy_058;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0077 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb068_alpha_dummy_045))).fv ∪
                        ((Class.cv (nb068_alpha_dummy_046))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪
                        ((Class.cv (nb068_alpha_dummy_049 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068_split_alpha_0037 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068_split_alpha_0037 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb068_alpha_dummy_085), (nb068_alpha_dummy_086 f)),
                            ((nb068_alpha_dummy_054), (nb068_alpha_dummy_056 f)),
                            ((nb068_alpha_dummy_053), (nb068_alpha_dummy_055 f)),
                            ((nb068_alpha_dummy_083), (nb068_alpha_dummy_084 f)),
                            ((nb068_alpha_dummy_057), (nb068_alpha_dummy_058 f)),
                            ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
                            ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
                            ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
                            ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                            ((nb068_alpha_dummy_001), x),
                            ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

@[expose]
noncomputable def nb068_split_alpha_0039 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_105), (nb068_alpha_dummy_108 f)),
        ((nb068_alpha_dummy_104), (nb068_alpha_dummy_107 f)),
        ((nb068_alpha_dummy_103), (nb068_alpha_dummy_106 f)),
        ((nb068_alpha_dummy_101), (nb068_alpha_dummy_102 f)),
        ((nb068_alpha_dummy_097), (nb068_alpha_dummy_099 f)),
        ((nb068_alpha_dummy_098), (nb068_alpha_dummy_100 f)),
        ((nb068_alpha_dummy_090), (nb068_alpha_dummy_092 f)),
        ((nb068_alpha_dummy_089), (nb068_alpha_dummy_091 f)),
        ((nb068_alpha_dummy_095), (nb068_alpha_dummy_096 f)),
        ((nb068_alpha_dummy_093), (nb068_alpha_dummy_094 f)),
        ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
        ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
        ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
        ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb068_alpha_dummy_104)) (Class.cv (nb068_alpha_dummy_105)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_103))
            (syn_cun (Class.cv (nb068_alpha_dummy_104)) (Class.cv (nb068_alpha_dummy_105))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_107 f))
            (Class.cv (nb068_alpha_dummy_108 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_106 f))
            (syn_cun (Class.cv (nb068_alpha_dummy_107 f))
              (Class.cv (nb068_alpha_dummy_108 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_104) ≠ (nb068_alpha_dummy_111) from (by
                              unfold nb068_alpha_dummy_111;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0098) 0))))
                          (show (nb068_alpha_dummy_107 f) ≠ (nb068_alpha_dummy_112 f) from (by
                              unfold nb068_alpha_dummy_112;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0099 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_104) ≠ (nb068_alpha_dummy_109) from (by
                                unfold nb068_alpha_dummy_109;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0096) 0))))
                            (show (nb068_alpha_dummy_107 f) ≠ (nb068_alpha_dummy_110 f) from (by
                                unfold nb068_alpha_dummy_110;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0097 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_097))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_099 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_105) ≠ (nb068_alpha_dummy_111) from (by
                              unfold nb068_alpha_dummy_111;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0102) 0))))
                          (show (nb068_alpha_dummy_108 f) ≠ (nb068_alpha_dummy_112 f) from (by
                              unfold nb068_alpha_dummy_112;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0103 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_105) ≠ (nb068_alpha_dummy_109) from (by
                                unfold nb068_alpha_dummy_109;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0100) 0))))
                            (show (nb068_alpha_dummy_108 f) ≠ (nb068_alpha_dummy_110 f) from (by
                                unfold nb068_alpha_dummy_110;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0101 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_104) ≠ (nb068_alpha_dummy_111) from (by
                              unfold nb068_alpha_dummy_111;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0098) 0))))
                          (show (nb068_alpha_dummy_107 f) ≠ (nb068_alpha_dummy_112 f) from (by
                              unfold nb068_alpha_dummy_112;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0099 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_104) ≠ (nb068_alpha_dummy_109) from (by
                                unfold nb068_alpha_dummy_109;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0096) 0))))
                            (show (nb068_alpha_dummy_107 f) ≠ (nb068_alpha_dummy_110 f) from (by
                                unfold nb068_alpha_dummy_110;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0097 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_097))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_099 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_105) ≠ (nb068_alpha_dummy_111) from (by
                              unfold nb068_alpha_dummy_111;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0102) 0))))
                          (show (nb068_alpha_dummy_108 f) ≠ (nb068_alpha_dummy_112 f) from (by
                              unfold nb068_alpha_dummy_112;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0103 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_105) ≠ (nb068_alpha_dummy_109) from (by
                                unfold nb068_alpha_dummy_109;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0100) 0))))
                            (show (nb068_alpha_dummy_108 f) ≠ (nb068_alpha_dummy_110 f) from (by
                                unfold nb068_alpha_dummy_110;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0101 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb068_alpha_dummy_105), (nb068_alpha_dummy_108 f)),
          ((nb068_alpha_dummy_104), (nb068_alpha_dummy_107 f)),
          ((nb068_alpha_dummy_103), (nb068_alpha_dummy_106 f)),
          ((nb068_alpha_dummy_101), (nb068_alpha_dummy_102 f)),
          ((nb068_alpha_dummy_097), (nb068_alpha_dummy_099 f)),
          ((nb068_alpha_dummy_098), (nb068_alpha_dummy_100 f)),
          ((nb068_alpha_dummy_090), (nb068_alpha_dummy_092 f)),
          ((nb068_alpha_dummy_089), (nb068_alpha_dummy_091 f)),
          ((nb068_alpha_dummy_095), (nb068_alpha_dummy_096 f)),
          ((nb068_alpha_dummy_093), (nb068_alpha_dummy_094 f)),
          ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
          ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
          ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
          ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
          ((nb068_alpha_dummy_001), x),
          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_097))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068_alpha_dummy_099 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_097))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_099 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_104) ≠ (nb068_alpha_dummy_115) from (by
                                unfold nb068_alpha_dummy_115;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0106) 0))))
                            (show (nb068_alpha_dummy_107 f) ≠ (nb068_alpha_dummy_116 f) from (by
                                unfold nb068_alpha_dummy_116;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0107 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_104) ≠ (nb068_alpha_dummy_113) from (by
                                  unfold nb068_alpha_dummy_113;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0104) 0))))
                              (show (nb068_alpha_dummy_107 f) ≠ (nb068_alpha_dummy_114 f) from
                                (by
                                  unfold nb068_alpha_dummy_114;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0105 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_097))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_099 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_104) ≠ (nb068_alpha_dummy_115) from (by
                                unfold nb068_alpha_dummy_115;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0106) 0))))
                            (show (nb068_alpha_dummy_107 f) ≠ (nb068_alpha_dummy_116 f) from (by
                                unfold nb068_alpha_dummy_116;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0107 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_104) ≠ (nb068_alpha_dummy_113) from (by
                                  unfold nb068_alpha_dummy_113;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0104) 0))))
                              (show (nb068_alpha_dummy_107 f) ≠ (nb068_alpha_dummy_114 f) from
                                (by
                                  unfold nb068_alpha_dummy_114;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0105 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_097))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_099 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_105) ≠ (nb068_alpha_dummy_117) from (by
                                unfold nb068_alpha_dummy_117;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0110) 0))))
                            (show (nb068_alpha_dummy_108 f) ≠ (nb068_alpha_dummy_118 f) from (by
                                unfold nb068_alpha_dummy_118;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0111 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_105) ≠ (nb068_alpha_dummy_113) from (by
                                  unfold nb068_alpha_dummy_113;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0108) 0))))
                              (show (nb068_alpha_dummy_108 f) ≠ (nb068_alpha_dummy_114 f) from
                                (by
                                  unfold nb068_alpha_dummy_114;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0109 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_105) ≠ (nb068_alpha_dummy_117) from (by
                                unfold nb068_alpha_dummy_117;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0110) 0))))
                            (show (nb068_alpha_dummy_108 f) ≠ (nb068_alpha_dummy_118 f) from (by
                                unfold nb068_alpha_dummy_118;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0111 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_105) ≠ (nb068_alpha_dummy_113) from (by
                                  unfold nb068_alpha_dummy_113;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0108) 0))))
                              (show (nb068_alpha_dummy_108 f) ≠ (nb068_alpha_dummy_114 f) from
                                (by
                                  unfold nb068_alpha_dummy_114;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0109 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part025`. -/


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
noncomputable def nb068_split_alpha_0040 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_090), (nb068_alpha_dummy_092 f)),
        ((nb068_alpha_dummy_089), (nb068_alpha_dummy_091 f)),
        ((nb068_alpha_dummy_095), (nb068_alpha_dummy_096 f)),
        ((nb068_alpha_dummy_093), (nb068_alpha_dummy_094 f)),
        ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
        ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
        ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
        ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.classEq (Class.cv (nb068_alpha_dummy_089))
        (syn_cphi (Class.cv (nb068_alpha_dummy_090))))
      (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f))
        (syn_cphi (Class.cv (nb068_alpha_dummy_092 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb068_alpha_dummy_045))).fv ∪ ((Class.cv (nb068_alpha_dummy_047))).fv)
          (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪
            ((Class.cv (nb068_alpha_dummy_050 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (show (nb068_alpha_dummy_090) ≠ (nb068_alpha_dummy_097) from (by
                    unfold nb068_alpha_dummy_097;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0090) 0))))
                (show (nb068_alpha_dummy_092 f) ≠ (nb068_alpha_dummy_099 f) from (by
                    unfold nb068_alpha_dummy_099;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0091 f) 0))))
                (TAlphaVar.there (show (nb068_alpha_dummy_090) ≠ (nb068_alpha_dummy_098) from
                    (by
                      unfold nb068_alpha_dummy_098;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0090) 1))))
                  (show (nb068_alpha_dummy_092 f) ≠ (nb068_alpha_dummy_100 f) from (by
                      unfold nb068_alpha_dummy_100;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0091 f) 1))))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb068_alpha_dummy_090))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb068_alpha_dummy_092 f))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb068_alpha_dummy_097) ≠ (nb068_alpha_dummy_104) from
                                    (by
                                      unfold nb068_alpha_dummy_104;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0094)
                                              1)))) (show
                                    (nb068_alpha_dummy_099 f) ≠ (nb068_alpha_dummy_107 f) from
                                    (by
                                      unfold nb068_alpha_dummy_107;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0095 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb068_alpha_dummy_097) ≠ (nb068_alpha_dummy_103) from (by
                                        unfold nb068_alpha_dummy_103;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0094)
                                                0)))) (show (nb068_alpha_dummy_099 f) ≠
                                        (nb068_alpha_dummy_106 f) from (by
                                        unfold nb068_alpha_dummy_106;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0095 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068_alpha_dummy_097) ≠ (nb068_alpha_dummy_101) from
                                        (by
                                          unfold nb068_alpha_dummy_101;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0092)
                                                  0)))) (show (nb068_alpha_dummy_099 f) ≠
        (nb068_alpha_dummy_102 f) from (by
                                          unfold nb068_alpha_dummy_102;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0093 f) 0))))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.refl_of_closed
                                    [((nb068_alpha_dummy_105), (nb068_alpha_dummy_108 f)),
                                      ((nb068_alpha_dummy_104), (nb068_alpha_dummy_107 f)),
                                      ((nb068_alpha_dummy_103), (nb068_alpha_dummy_106 f)),
                                      ((nb068_alpha_dummy_101), (nb068_alpha_dummy_102 f)),
                                      ((nb068_alpha_dummy_097), (nb068_alpha_dummy_099 f)),
                                      ((nb068_alpha_dummy_098), (nb068_alpha_dummy_100 f)),
                                      ((nb068_alpha_dummy_090), (nb068_alpha_dummy_092 f)),
                                      ((nb068_alpha_dummy_089), (nb068_alpha_dummy_091 f)),
                                      ((nb068_alpha_dummy_095), (nb068_alpha_dummy_096 f)),
                                      ((nb068_alpha_dummy_093), (nb068_alpha_dummy_094 f)),
                                      ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
                                      ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
                                      ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
                                      ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
                                      ((nb068_alpha_dummy_000), f),
                                      ((nb068_alpha_dummy_002), y),
                                      ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003),
                                        (nb068_alpha_dummy_004 x y f))]
                                    (syn_c1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb068_split_alpha_0039 x y f))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (show (nb068_alpha_dummy_097) ≠ (nb068_alpha_dummy_101) from (by
                              unfold nb068_alpha_dummy_101;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0092) 0))))
                          (show (nb068_alpha_dummy_099 f) ≠ (nb068_alpha_dummy_102 f) from (by
                              unfold nb068_alpha_dummy_102;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0093 f) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb068_alpha_dummy_101), (nb068_alpha_dummy_102 f)),
                          ((nb068_alpha_dummy_097), (nb068_alpha_dummy_099 f)),
                          ((nb068_alpha_dummy_098), (nb068_alpha_dummy_100 f)),
                          ((nb068_alpha_dummy_090), (nb068_alpha_dummy_092 f)),
                          ((nb068_alpha_dummy_089), (nb068_alpha_dummy_091 f)),
                          ((nb068_alpha_dummy_095), (nb068_alpha_dummy_096 f)),
                          ((nb068_alpha_dummy_093), (nb068_alpha_dummy_094 f)),
                          ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
                          ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
                          ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
                          ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
                          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                          ((nb068_alpha_dummy_001), x),
                          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb068_alpha_dummy_097) ≠ (nb068_alpha_dummy_101) from (by
                            unfold nb068_alpha_dummy_101;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0092) 0))))
                        (show (nb068_alpha_dummy_099 f) ≠ (nb068_alpha_dummy_102 f) from (by
                            unfold nb068_alpha_dummy_102;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0093 f) 0))))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (show (nb068_alpha_dummy_097) ≠ (nb068_alpha_dummy_101) from (by
                              unfold nb068_alpha_dummy_101;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0092) 0))))
                          (show (nb068_alpha_dummy_099 f) ≠ (nb068_alpha_dummy_102 f) from (by
                              unfold nb068_alpha_dummy_102;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0093 f) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb068_alpha_dummy_101), (nb068_alpha_dummy_102 f)),
                          ((nb068_alpha_dummy_097), (nb068_alpha_dummy_099 f)),
                          ((nb068_alpha_dummy_098), (nb068_alpha_dummy_100 f)),
                          ((nb068_alpha_dummy_090), (nb068_alpha_dummy_092 f)),
                          ((nb068_alpha_dummy_089), (nb068_alpha_dummy_091 f)),
                          ((nb068_alpha_dummy_095), (nb068_alpha_dummy_096 f)),
                          ((nb068_alpha_dummy_093), (nb068_alpha_dummy_094 f)),
                          ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
                          ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
                          ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
                          ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
                          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                          ((nb068_alpha_dummy_001), x),
                          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))

@[expose]
noncomputable def nb068_split_alpha_0041 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_105), (nb068_alpha_dummy_108 f)),
        ((nb068_alpha_dummy_104), (nb068_alpha_dummy_107 f)),
        ((nb068_alpha_dummy_103), (nb068_alpha_dummy_106 f)),
        ((nb068_alpha_dummy_101), (nb068_alpha_dummy_102 f)),
        ((nb068_alpha_dummy_097), (nb068_alpha_dummy_099 f)),
        ((nb068_alpha_dummy_098), (nb068_alpha_dummy_100 f)),
        ((nb068_alpha_dummy_123), (nb068_alpha_dummy_124 f)),
        ((nb068_alpha_dummy_121), (nb068_alpha_dummy_122 f)),
        ((nb068_alpha_dummy_090), (nb068_alpha_dummy_092 f)),
        ((nb068_alpha_dummy_089), (nb068_alpha_dummy_091 f)),
        ((nb068_alpha_dummy_119), (nb068_alpha_dummy_120 f)),
        ((nb068_alpha_dummy_093), (nb068_alpha_dummy_094 f)),
        ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
        ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
        ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
        ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb068_alpha_dummy_104)) (Class.cv (nb068_alpha_dummy_105)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_103))
            (syn_cun (Class.cv (nb068_alpha_dummy_104)) (Class.cv (nb068_alpha_dummy_105))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_107 f))
            (Class.cv (nb068_alpha_dummy_108 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_106 f))
            (syn_cun (Class.cv (nb068_alpha_dummy_107 f))
              (Class.cv (nb068_alpha_dummy_108 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_104) ≠ (nb068_alpha_dummy_111) from (by
                              unfold nb068_alpha_dummy_111;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0098) 0))))
                          (show (nb068_alpha_dummy_107 f) ≠ (nb068_alpha_dummy_112 f) from (by
                              unfold nb068_alpha_dummy_112;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0099 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_104) ≠ (nb068_alpha_dummy_109) from (by
                                unfold nb068_alpha_dummy_109;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0096) 0))))
                            (show (nb068_alpha_dummy_107 f) ≠ (nb068_alpha_dummy_110 f) from (by
                                unfold nb068_alpha_dummy_110;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0097 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_097))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_099 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_105) ≠ (nb068_alpha_dummy_111) from (by
                              unfold nb068_alpha_dummy_111;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0102) 0))))
                          (show (nb068_alpha_dummy_108 f) ≠ (nb068_alpha_dummy_112 f) from (by
                              unfold nb068_alpha_dummy_112;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0103 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_105) ≠ (nb068_alpha_dummy_109) from (by
                                unfold nb068_alpha_dummy_109;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0100) 0))))
                            (show (nb068_alpha_dummy_108 f) ≠ (nb068_alpha_dummy_110 f) from (by
                                unfold nb068_alpha_dummy_110;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0101 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_104) ≠ (nb068_alpha_dummy_111) from (by
                              unfold nb068_alpha_dummy_111;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0098) 0))))
                          (show (nb068_alpha_dummy_107 f) ≠ (nb068_alpha_dummy_112 f) from (by
                              unfold nb068_alpha_dummy_112;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0099 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_104) ≠ (nb068_alpha_dummy_109) from (by
                                unfold nb068_alpha_dummy_109;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0096) 0))))
                            (show (nb068_alpha_dummy_107 f) ≠ (nb068_alpha_dummy_110 f) from (by
                                unfold nb068_alpha_dummy_110;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0097 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_097))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_099 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_105) ≠ (nb068_alpha_dummy_111) from (by
                              unfold nb068_alpha_dummy_111;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0102) 0))))
                          (show (nb068_alpha_dummy_108 f) ≠ (nb068_alpha_dummy_112 f) from (by
                              unfold nb068_alpha_dummy_112;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0103 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_105) ≠ (nb068_alpha_dummy_109) from (by
                                unfold nb068_alpha_dummy_109;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0100) 0))))
                            (show (nb068_alpha_dummy_108 f) ≠ (nb068_alpha_dummy_110 f) from (by
                                unfold nb068_alpha_dummy_110;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0101 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb068_alpha_dummy_105), (nb068_alpha_dummy_108 f)),
          ((nb068_alpha_dummy_104), (nb068_alpha_dummy_107 f)),
          ((nb068_alpha_dummy_103), (nb068_alpha_dummy_106 f)),
          ((nb068_alpha_dummy_101), (nb068_alpha_dummy_102 f)),
          ((nb068_alpha_dummy_097), (nb068_alpha_dummy_099 f)),
          ((nb068_alpha_dummy_098), (nb068_alpha_dummy_100 f)),
          ((nb068_alpha_dummy_123), (nb068_alpha_dummy_124 f)),
          ((nb068_alpha_dummy_121), (nb068_alpha_dummy_122 f)),
          ((nb068_alpha_dummy_090), (nb068_alpha_dummy_092 f)),
          ((nb068_alpha_dummy_089), (nb068_alpha_dummy_091 f)),
          ((nb068_alpha_dummy_119), (nb068_alpha_dummy_120 f)),
          ((nb068_alpha_dummy_093), (nb068_alpha_dummy_094 f)),
          ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
          ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
          ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
          ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
          ((nb068_alpha_dummy_001), x),
          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_097))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068_alpha_dummy_099 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_097))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_099 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_104) ≠ (nb068_alpha_dummy_115) from (by
                                unfold nb068_alpha_dummy_115;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0106) 0))))
                            (show (nb068_alpha_dummy_107 f) ≠ (nb068_alpha_dummy_116 f) from (by
                                unfold nb068_alpha_dummy_116;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0107 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_104) ≠ (nb068_alpha_dummy_113) from (by
                                  unfold nb068_alpha_dummy_113;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0104) 0))))
                              (show (nb068_alpha_dummy_107 f) ≠ (nb068_alpha_dummy_114 f) from
                                (by
                                  unfold nb068_alpha_dummy_114;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0105 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_097))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_099 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_104) ≠ (nb068_alpha_dummy_115) from (by
                                unfold nb068_alpha_dummy_115;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0106) 0))))
                            (show (nb068_alpha_dummy_107 f) ≠ (nb068_alpha_dummy_116 f) from (by
                                unfold nb068_alpha_dummy_116;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0107 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_104) ≠ (nb068_alpha_dummy_113) from (by
                                  unfold nb068_alpha_dummy_113;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0104) 0))))
                              (show (nb068_alpha_dummy_107 f) ≠ (nb068_alpha_dummy_114 f) from
                                (by
                                  unfold nb068_alpha_dummy_114;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0105 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_097))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_099 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_105) ≠ (nb068_alpha_dummy_117) from (by
                                unfold nb068_alpha_dummy_117;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0110) 0))))
                            (show (nb068_alpha_dummy_108 f) ≠ (nb068_alpha_dummy_118 f) from (by
                                unfold nb068_alpha_dummy_118;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0111 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_105) ≠ (nb068_alpha_dummy_113) from (by
                                  unfold nb068_alpha_dummy_113;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0108) 0))))
                              (show (nb068_alpha_dummy_108 f) ≠ (nb068_alpha_dummy_114 f) from
                                (by
                                  unfold nb068_alpha_dummy_114;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0109 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_105) ≠ (nb068_alpha_dummy_117) from (by
                                unfold nb068_alpha_dummy_117;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0110) 0))))
                            (show (nb068_alpha_dummy_108 f) ≠ (nb068_alpha_dummy_118 f) from (by
                                unfold nb068_alpha_dummy_118;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0111 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_105) ≠ (nb068_alpha_dummy_113) from (by
                                  unfold nb068_alpha_dummy_113;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0108) 0))))
                              (show (nb068_alpha_dummy_108 f) ≠ (nb068_alpha_dummy_114 f) from
                                (by
                                  unfold nb068_alpha_dummy_114;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0109 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb068_split_alpha_0042 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_097), (nb068_alpha_dummy_099 f)),
        ((nb068_alpha_dummy_098), (nb068_alpha_dummy_100 f)),
        ((nb068_alpha_dummy_123), (nb068_alpha_dummy_124 f)),
        ((nb068_alpha_dummy_121), (nb068_alpha_dummy_122 f)),
        ((nb068_alpha_dummy_090), (nb068_alpha_dummy_092 f)),
        ((nb068_alpha_dummy_089), (nb068_alpha_dummy_091 f)),
        ((nb068_alpha_dummy_119), (nb068_alpha_dummy_120 f)),
        ((nb068_alpha_dummy_093), (nb068_alpha_dummy_094 f)),
        ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
        ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
        ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
        ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_097))
          (Class.cv (nb068_alpha_dummy_090))) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_098))
            (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_097)) (syn_cnnc))
              (syn_cplc (Class.cv (nb068_alpha_dummy_097)) (syn_c1c))
              (Class.cv (nb068_alpha_dummy_097))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_099 f))
          (Class.cv (nb068_alpha_dummy_092 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_100 f))
            (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_099 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb068_alpha_dummy_099 f)) (syn_c1c))
              (Class.cv (nb068_alpha_dummy_099 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068_alpha_dummy_090) ≠ (nb068_alpha_dummy_097) from (by
              unfold nb068_alpha_dummy_097;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0090) 0))))
          (show (nb068_alpha_dummy_092 f) ≠ (nb068_alpha_dummy_099 f) from (by
              unfold nb068_alpha_dummy_099;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0091 f) 0))))
          (TAlphaVar.there (show (nb068_alpha_dummy_090) ≠ (nb068_alpha_dummy_098) from (by
                unfold nb068_alpha_dummy_098;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0090) 1))))
            (show (nb068_alpha_dummy_092 f) ≠ (nb068_alpha_dummy_100 f) from (by
                unfold nb068_alpha_dummy_100;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0091 f) 1))))
            (TAlphaVar.there (show (nb068_alpha_dummy_090) ≠ (nb068_alpha_dummy_123) from (by
                  unfold nb068_alpha_dummy_123;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0120) 0))))
              (show (nb068_alpha_dummy_092 f) ≠ (nb068_alpha_dummy_124 f) from (by
                  unfold nb068_alpha_dummy_124;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0121 f) 0))))
              (TAlphaVar.there (show (nb068_alpha_dummy_090) ≠ (nb068_alpha_dummy_121) from (by
                    unfold nb068_alpha_dummy_121;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0118) 0))))
                (show (nb068_alpha_dummy_092 f) ≠ (nb068_alpha_dummy_122 f) from (by
                    unfold nb068_alpha_dummy_122;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0119 f) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_090))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_092 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068_alpha_dummy_097) ≠ (nb068_alpha_dummy_104) from (by
                                  unfold nb068_alpha_dummy_104;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0094) 1))))
                              (show (nb068_alpha_dummy_099 f) ≠ (nb068_alpha_dummy_107 f) from
                                (by
                                  unfold nb068_alpha_dummy_107;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0095 f) 1))))
                              (TAlphaVar.there
                                (show (nb068_alpha_dummy_097) ≠ (nb068_alpha_dummy_103) from (by
                                    unfold nb068_alpha_dummy_103;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0094) 0)))) (show
                                  (nb068_alpha_dummy_099 f) ≠ (nb068_alpha_dummy_106 f) from (by
                                    unfold nb068_alpha_dummy_106;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0095 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb068_alpha_dummy_097) ≠ (nb068_alpha_dummy_101) from
                                    (by
                                      unfold nb068_alpha_dummy_101;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0092)
                                              0)))) (show
                                    (nb068_alpha_dummy_099 f) ≠ (nb068_alpha_dummy_102 f) from
                                    (by
                                      unfold nb068_alpha_dummy_102;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0093 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb068_alpha_dummy_105), (nb068_alpha_dummy_108 f)),
                                  ((nb068_alpha_dummy_104), (nb068_alpha_dummy_107 f)),
                                  ((nb068_alpha_dummy_103), (nb068_alpha_dummy_106 f)),
                                  ((nb068_alpha_dummy_101), (nb068_alpha_dummy_102 f)),
                                  ((nb068_alpha_dummy_097), (nb068_alpha_dummy_099 f)),
                                  ((nb068_alpha_dummy_098), (nb068_alpha_dummy_100 f)),
                                  ((nb068_alpha_dummy_123), (nb068_alpha_dummy_124 f)),
                                  ((nb068_alpha_dummy_121), (nb068_alpha_dummy_122 f)),
                                  ((nb068_alpha_dummy_090), (nb068_alpha_dummy_092 f)),
                                  ((nb068_alpha_dummy_089), (nb068_alpha_dummy_091 f)),
                                  ((nb068_alpha_dummy_119), (nb068_alpha_dummy_120 f)),
                                  ((nb068_alpha_dummy_093), (nb068_alpha_dummy_094 f)),
                                  ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
                                  ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
                                  ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
                                  ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
                                  ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                                  ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003),
                                    (nb068_alpha_dummy_004 x y f))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb068_split_alpha_0041 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb068_alpha_dummy_097) ≠ (nb068_alpha_dummy_101) from (by
                          unfold nb068_alpha_dummy_101;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0092) 0))))
                      (show (nb068_alpha_dummy_099 f) ≠ (nb068_alpha_dummy_102 f) from (by
                          unfold nb068_alpha_dummy_102;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0093 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb068_alpha_dummy_101), (nb068_alpha_dummy_102 f)),
                      ((nb068_alpha_dummy_097), (nb068_alpha_dummy_099 f)),
                      ((nb068_alpha_dummy_098), (nb068_alpha_dummy_100 f)),
                      ((nb068_alpha_dummy_123), (nb068_alpha_dummy_124 f)),
                      ((nb068_alpha_dummy_121), (nb068_alpha_dummy_122 f)),
                      ((nb068_alpha_dummy_090), (nb068_alpha_dummy_092 f)),
                      ((nb068_alpha_dummy_089), (nb068_alpha_dummy_091 f)),
                      ((nb068_alpha_dummy_119), (nb068_alpha_dummy_120 f)),
                      ((nb068_alpha_dummy_093), (nb068_alpha_dummy_094 f)),
                      ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
                      ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
                      ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
                      ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
                      ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                      ((nb068_alpha_dummy_001), x),
                      ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068_alpha_dummy_097) ≠ (nb068_alpha_dummy_101) from
                      (by
                        unfold nb068_alpha_dummy_101;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0092) 0))))
                    (show (nb068_alpha_dummy_099 f) ≠ (nb068_alpha_dummy_102 f) from (by
                        unfold nb068_alpha_dummy_102;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0093 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068_alpha_dummy_097) ≠ (nb068_alpha_dummy_101) from (by
                          unfold nb068_alpha_dummy_101;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0092) 0))))
                      (show (nb068_alpha_dummy_099 f) ≠ (nb068_alpha_dummy_102 f) from (by
                          unfold nb068_alpha_dummy_102;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0093 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb068_alpha_dummy_101), (nb068_alpha_dummy_102 f)),
                      ((nb068_alpha_dummy_097), (nb068_alpha_dummy_099 f)),
                      ((nb068_alpha_dummy_098), (nb068_alpha_dummy_100 f)),
                      ((nb068_alpha_dummy_123), (nb068_alpha_dummy_124 f)),
                      ((nb068_alpha_dummy_121), (nb068_alpha_dummy_122 f)),
                      ((nb068_alpha_dummy_090), (nb068_alpha_dummy_092 f)),
                      ((nb068_alpha_dummy_089), (nb068_alpha_dummy_091 f)),
                      ((nb068_alpha_dummy_119), (nb068_alpha_dummy_120 f)),
                      ((nb068_alpha_dummy_093), (nb068_alpha_dummy_094 f)),
                      ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
                      ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
                      ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
                      ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
                      ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                      ((nb068_alpha_dummy_001), x),
                      ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb068_split_alpha_0043 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_119), (nb068_alpha_dummy_120 f)),
        ((nb068_alpha_dummy_093), (nb068_alpha_dummy_094 f)),
        ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
        ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
        ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
        ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_119))
          (Class.cab (nb068_alpha_dummy_089)
            (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_047))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_089))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_090))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb068_alpha_dummy_119))
            (Class.cab (nb068_alpha_dummy_089)
              (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_047))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_089))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_090)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_120 f))
          (Class.cab (nb068_alpha_dummy_091 f)
            (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_050 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_092 f)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb068_alpha_dummy_120 f))
            (Class.cab (nb068_alpha_dummy_091 f)
              (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_050 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_092 f)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb068_alpha_dummy_047) ≠ (nb068_alpha_dummy_090) from
                    (by
                      unfold nb068_alpha_dummy_090;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0112) 1))))
                  (show (nb068_alpha_dummy_050 f) ≠ (nb068_alpha_dummy_092 f) from (by
                      unfold nb068_alpha_dummy_092;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0114 f) 1))))
                  (TAlphaVar.there (show (nb068_alpha_dummy_047) ≠ (nb068_alpha_dummy_089) from
                      (by
                        unfold nb068_alpha_dummy_089;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0112) 0))))
                    (show (nb068_alpha_dummy_050 f) ≠ (nb068_alpha_dummy_091 f) from (by
                        unfold nb068_alpha_dummy_091;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0114 f) 0)))) (TAlphaVar.there
                      (show (nb068_alpha_dummy_047) ≠ (nb068_alpha_dummy_119) from (by
                          unfold nb068_alpha_dummy_119;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0116) 0))))
                      (show (nb068_alpha_dummy_050 f) ≠ (nb068_alpha_dummy_120 f) from (by
                          unfold nb068_alpha_dummy_120;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0117 f) 0))))
                      (TAlphaVar.there
                        (show (nb068_alpha_dummy_047) ≠ (nb068_alpha_dummy_093) from (by
                            unfold nb068_alpha_dummy_093;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0113) 0))))
                        (show (nb068_alpha_dummy_050 f) ≠ (nb068_alpha_dummy_094 f) from (by
                            unfold nb068_alpha_dummy_094;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0115 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_045))).fv ∪
                      ((Class.cv (nb068_alpha_dummy_047))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪
                      ((Class.cv (nb068_alpha_dummy_050 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068_split_alpha_0042 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068_split_alpha_0042 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb068_alpha_dummy_121), (nb068_alpha_dummy_122 f)),
                          ((nb068_alpha_dummy_090), (nb068_alpha_dummy_092 f)),
                          ((nb068_alpha_dummy_089), (nb068_alpha_dummy_091 f)),
                          ((nb068_alpha_dummy_119), (nb068_alpha_dummy_120 f)),
                          ((nb068_alpha_dummy_093), (nb068_alpha_dummy_094 f)),
                          ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
                          ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
                          ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
                          ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
                          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                          ((nb068_alpha_dummy_001), x),
                          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068_alpha_dummy_047) ≠ (nb068_alpha_dummy_090) from
                      (by
                        unfold nb068_alpha_dummy_090;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0112) 1))))
                    (show (nb068_alpha_dummy_050 f) ≠ (nb068_alpha_dummy_092 f) from (by
                        unfold nb068_alpha_dummy_092;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0114 f) 1)))) (TAlphaVar.there
                      (show (nb068_alpha_dummy_047) ≠ (nb068_alpha_dummy_089) from (by
                          unfold nb068_alpha_dummy_089;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0112) 0))))
                      (show (nb068_alpha_dummy_050 f) ≠ (nb068_alpha_dummy_091 f) from (by
                          unfold nb068_alpha_dummy_091;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0114 f) 0))))
                      (TAlphaVar.there
                        (show (nb068_alpha_dummy_047) ≠ (nb068_alpha_dummy_119) from (by
                            unfold nb068_alpha_dummy_119;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0116) 0))))
                        (show (nb068_alpha_dummy_050 f) ≠ (nb068_alpha_dummy_120 f) from (by
                            unfold nb068_alpha_dummy_120;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0117 f) 0))))
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_047) ≠ (nb068_alpha_dummy_093) from (by
                              unfold nb068_alpha_dummy_093;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0113) 0))))
                          (show (nb068_alpha_dummy_050 f) ≠ (nb068_alpha_dummy_094 f) from (by
                              unfold nb068_alpha_dummy_094;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0115 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb068_alpha_dummy_045))).fv ∪
                        ((Class.cv (nb068_alpha_dummy_047))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪
                        ((Class.cv (nb068_alpha_dummy_050 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068_split_alpha_0042 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068_split_alpha_0042 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb068_alpha_dummy_121), (nb068_alpha_dummy_122 f)),
                            ((nb068_alpha_dummy_090), (nb068_alpha_dummy_092 f)),
                            ((nb068_alpha_dummy_089), (nb068_alpha_dummy_091 f)),
                            ((nb068_alpha_dummy_119), (nb068_alpha_dummy_120 f)),
                            ((nb068_alpha_dummy_093), (nb068_alpha_dummy_094 f)),
                            ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
                            ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
                            ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
                            ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
                            ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                            ((nb068_alpha_dummy_001), x),
                            ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part026`. -/


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
noncomputable def nb068_split_alpha_0044 (x : Var) (y : Var) (f : Var) :
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
        ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
        ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
        ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
        ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
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
          ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
          ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
          ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
          ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
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
noncomputable def nb068_split_alpha_0045 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_139), (nb068_alpha_dummy_141 f)),
        ((nb068_alpha_dummy_140), (nb068_alpha_dummy_142 f)),
        ((nb068_alpha_dummy_132), (nb068_alpha_dummy_134 f)),
        ((nb068_alpha_dummy_131), (nb068_alpha_dummy_133 f)),
        ((nb068_alpha_dummy_137), (nb068_alpha_dummy_138 f)),
        ((nb068_alpha_dummy_135), (nb068_alpha_dummy_136 f)),
        ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
        ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
        ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
        ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
        ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
        ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
        ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_139))
          (Class.cv (nb068_alpha_dummy_132))) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_140))
            (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_139)) (syn_cnnc))
              (syn_cplc (Class.cv (nb068_alpha_dummy_139)) (syn_c1c))
              (Class.cv (nb068_alpha_dummy_139))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_141 f))
          (Class.cv (nb068_alpha_dummy_134 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_142 f))
            (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_141 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb068_alpha_dummy_141 f)) (syn_c1c))
              (Class.cv (nb068_alpha_dummy_141 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068_alpha_dummy_132) ≠ (nb068_alpha_dummy_139) from (by
              unfold nb068_alpha_dummy_139;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0132) 0))))
          (show (nb068_alpha_dummy_134 f) ≠ (nb068_alpha_dummy_141 f) from (by
              unfold nb068_alpha_dummy_141;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0133 f) 0))))
          (TAlphaVar.there (show (nb068_alpha_dummy_132) ≠ (nb068_alpha_dummy_140) from (by
                unfold nb068_alpha_dummy_140;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0132) 1))))
            (show (nb068_alpha_dummy_134 f) ≠ (nb068_alpha_dummy_142 f) from (by
                unfold nb068_alpha_dummy_142;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0133 f) 1))))
            (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_132))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_134 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068_alpha_dummy_139) ≠ (nb068_alpha_dummy_146) from (by
                                  unfold nb068_alpha_dummy_146;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0136) 1))))
                              (show (nb068_alpha_dummy_141 f) ≠ (nb068_alpha_dummy_149 f) from
                                (by
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
                                          (mem_lt_freshVar (nb068_support_mem_0136) 0)))) (show
                                  (nb068_alpha_dummy_141 f) ≠ (nb068_alpha_dummy_148 f) from (by
                                    unfold nb068_alpha_dummy_148;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0137 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb068_alpha_dummy_139) ≠ (nb068_alpha_dummy_143) from
                                    (by
                                      unfold nb068_alpha_dummy_143;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0134)
                                              0)))) (show
                                    (nb068_alpha_dummy_141 f) ≠ (nb068_alpha_dummy_144 f) from
                                    (by
                                      unfold nb068_alpha_dummy_144;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0135 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
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
                                  ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
                                  ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
                                  ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
                                  ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
                                  ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                                  ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003),
                                    (nb068_alpha_dummy_004 x y f))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb068_split_alpha_0044 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
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
                      ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
                      ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
                      ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
                      ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
                      ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                      ((nb068_alpha_dummy_001), x),
                      ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068_alpha_dummy_139) ≠ (nb068_alpha_dummy_143) from
                      (by
                        unfold nb068_alpha_dummy_143;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0134) 0))))
                    (show (nb068_alpha_dummy_141 f) ≠ (nb068_alpha_dummy_144 f) from (by
                        unfold nb068_alpha_dummy_144;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
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
                      ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
                      ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
                      ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
                      ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
                      ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                      ((nb068_alpha_dummy_001), x),
                      ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb068_split_alpha_0046 (x : Var) (y : Var) (f : Var) :
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
        ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
        ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
        ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
        ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
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
          ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
          ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
          ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
          ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
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
noncomputable def nb068_split_alpha_0047 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_139), (nb068_alpha_dummy_141 f)),
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
        ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
        ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
        ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
        ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.classEq (Class.cv (nb068_alpha_dummy_140))
        (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_139)) (syn_cnnc))
          (syn_cplc (Class.cv (nb068_alpha_dummy_139)) (syn_c1c))
          (Class.cv (nb068_alpha_dummy_139))))
      (Wff.classEq (Class.cv (nb068_alpha_dummy_142 f))
        (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_141 f)) (syn_cnnc))
          (syn_cplc (Class.cv (nb068_alpha_dummy_141 f)) (syn_c1c))
          (Class.cv (nb068_alpha_dummy_141 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb068_alpha_dummy_132))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb068_alpha_dummy_134 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
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
                              (show (nb068_alpha_dummy_141 f) ≠ (nb068_alpha_dummy_144 f) from
                                (by
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
                              ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
                              ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
                              ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
                              ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
                              ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                              ((nb068_alpha_dummy_001), x),
                              ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                            (syn_c1c) (by simp only [fv_syn_c1c])))
                        (TAlphaWff.neg (nb068_split_alpha_0046 x y f)))))))) (TAlphaWff.classMem
              (TAlphaClass.cv (TAlphaVar.there
                  (show (nb068_alpha_dummy_139) ≠ (nb068_alpha_dummy_143) from (by
                      unfold nb068_alpha_dummy_143;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0134) 0))))
                  (show (nb068_alpha_dummy_141 f) ≠ (nb068_alpha_dummy_144 f) from (by
                      unfold nb068_alpha_dummy_144;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
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
                  ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
                  ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
                  ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
                  ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
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
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
                (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                (TAlphaVar.there (show (nb068_alpha_dummy_139) ≠ (nb068_alpha_dummy_143) from
                    (by
                      unfold nb068_alpha_dummy_143;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0134) 0))))
                  (show (nb068_alpha_dummy_141 f) ≠ (nb068_alpha_dummy_144 f) from (by
                      unfold nb068_alpha_dummy_144;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
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
                  ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
                  ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
                  ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
                  ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
                  ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                  ((nb068_alpha_dummy_001), x),
                  ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part027`. -/


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
noncomputable def nb068_split_alpha_0048 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_161), (nb068_alpha_dummy_162 f)),
        ((nb068_alpha_dummy_135), (nb068_alpha_dummy_136 f)),
        ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
        ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
        ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
        ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
        ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
        ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
        ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_161))
          (Class.cab (nb068_alpha_dummy_131)
            (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_126))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_131))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_132))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb068_alpha_dummy_161))
            (Class.cab (nb068_alpha_dummy_131)
              (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_126))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_131))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_132)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_162 f))
          (Class.cab (nb068_alpha_dummy_133 f)
            (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_128 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb068_alpha_dummy_162 f))
            (Class.cab (nb068_alpha_dummy_133 f)
              (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_128 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_132) from
                    (by
                      unfold nb068_alpha_dummy_132;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0154) 1))))
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
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0156 f) 0)))) (TAlphaVar.there
                      (show (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_161) from (by
                          unfold nb068_alpha_dummy_161;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0158) 0))))
                      (show (nb068_alpha_dummy_128 f) ≠ (nb068_alpha_dummy_162 f) from (by
                          unfold nb068_alpha_dummy_162;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0159 f) 0))))
                      (TAlphaVar.there
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
                  (nb068_support_mem_0161 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068_split_alpha_0047 x y f)))))
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
                  (nb068_support_mem_0161 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068_split_alpha_0047 x y f)))))))))
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
                          ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
                          ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
                          ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
                          ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
                          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                          ((nb068_alpha_dummy_001), x),
                          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_132) from
                      (by
                        unfold nb068_alpha_dummy_132;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0154) 1))))
                    (show (nb068_alpha_dummy_128 f) ≠ (nb068_alpha_dummy_134 f) from (by
                        unfold nb068_alpha_dummy_134;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0156 f) 1)))) (TAlphaVar.there
                      (show (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_131) from (by
                          unfold nb068_alpha_dummy_131;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0154) 0))))
                      (show (nb068_alpha_dummy_128 f) ≠ (nb068_alpha_dummy_133 f) from (by
                          unfold nb068_alpha_dummy_133;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0156 f) 0))))
                      (TAlphaVar.there
                        (show (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_161) from (by
                            unfold nb068_alpha_dummy_161;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0158) 0))))
                        (show (nb068_alpha_dummy_128 f) ≠ (nb068_alpha_dummy_162 f) from (by
                            unfold nb068_alpha_dummy_162;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0159 f) 0))))
                        (TAlphaVar.there
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
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb068_alpha_dummy_125))).fv ∪
                        ((Class.cv (nb068_alpha_dummy_126))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb068_alpha_dummy_127 f))).fv ∪
                        ((Class.cv (nb068_alpha_dummy_128 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068_alpha_dummy_132) ≠ (nb068_alpha_dummy_139) from (by
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
                  (nb068_support_mem_0163 f)
                  0)))) (TAlphaVar.there (show (nb068_alpha_dummy_132) ≠ (nb068_alpha_dummy_163)
        from (by
          unfold nb068_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0160)
                  0)))) (show (nb068_alpha_dummy_134 f) ≠ (nb068_alpha_dummy_164 f) from (by
          unfold nb068_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0161 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068_split_alpha_0047 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068_alpha_dummy_132) ≠ (nb068_alpha_dummy_139) from (by
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
                  (nb068_support_mem_0163 f)
                  0)))) (TAlphaVar.there (show (nb068_alpha_dummy_132) ≠ (nb068_alpha_dummy_163)
        from (by
          unfold nb068_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0160)
                  0)))) (show (nb068_alpha_dummy_134 f) ≠ (nb068_alpha_dummy_164 f) from (by
          unfold nb068_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0161 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068_split_alpha_0047 x y f)))))))))
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
                            ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
                            ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
                            ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
                            ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
                            ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                            ((nb068_alpha_dummy_001), x),
                            ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

@[expose]
noncomputable def nb068_split_alpha_0049 (x : Var) (y : Var) (f : Var) :
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
        ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
        ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
        ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
        ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
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
          ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
          ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
          ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
          ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
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
noncomputable def nb068_split_alpha_0050 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_175), (nb068_alpha_dummy_177 f)),
        ((nb068_alpha_dummy_176), (nb068_alpha_dummy_178 f)),
        ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)),
        ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)),
        ((nb068_alpha_dummy_173), (nb068_alpha_dummy_174 f)),
        ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)),
        ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
        ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
        ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
        ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
        ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
        ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
        ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_175))
          (Class.cv (nb068_alpha_dummy_168))) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_176))
            (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_175)) (syn_cnnc))
              (syn_cplc (Class.cv (nb068_alpha_dummy_175)) (syn_c1c))
              (Class.cv (nb068_alpha_dummy_175))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_177 f))
          (Class.cv (nb068_alpha_dummy_170 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_178 f))
            (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_177 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb068_alpha_dummy_177 f)) (syn_c1c))
              (Class.cv (nb068_alpha_dummy_177 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068_alpha_dummy_168) ≠ (nb068_alpha_dummy_175) from (by
              unfold nb068_alpha_dummy_175;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0170) 0))))
          (show (nb068_alpha_dummy_170 f) ≠ (nb068_alpha_dummy_177 f) from (by
              unfold nb068_alpha_dummy_177;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0171 f) 0))))
          (TAlphaVar.there (show (nb068_alpha_dummy_168) ≠ (nb068_alpha_dummy_176) from (by
                unfold nb068_alpha_dummy_176;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0170) 1))))
            (show (nb068_alpha_dummy_170 f) ≠ (nb068_alpha_dummy_178 f) from (by
                unfold nb068_alpha_dummy_178;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0171 f) 1))))
            (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_168))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_170 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068_alpha_dummy_175) ≠ (nb068_alpha_dummy_182) from (by
                                  unfold nb068_alpha_dummy_182;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0174) 1))))
                              (show (nb068_alpha_dummy_177 f) ≠ (nb068_alpha_dummy_185 f) from
                                (by
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
                                          (mem_lt_freshVar (nb068_support_mem_0174) 0)))) (show
                                  (nb068_alpha_dummy_177 f) ≠ (nb068_alpha_dummy_184 f) from (by
                                    unfold nb068_alpha_dummy_184;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0175 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb068_alpha_dummy_175) ≠ (nb068_alpha_dummy_179) from
                                    (by
                                      unfold nb068_alpha_dummy_179;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0172)
                                              0)))) (show
                                    (nb068_alpha_dummy_177 f) ≠ (nb068_alpha_dummy_180 f) from
                                    (by
                                      unfold nb068_alpha_dummy_180;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0173 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
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
                                  ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
                                  ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
                                  ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
                                  ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
                                  ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                                  ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003),
                                    (nb068_alpha_dummy_004 x y f))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb068_split_alpha_0049 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
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
                      ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
                      ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
                      ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
                      ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
                      ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                      ((nb068_alpha_dummy_001), x),
                      ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068_alpha_dummy_175) ≠ (nb068_alpha_dummy_179) from
                      (by
                        unfold nb068_alpha_dummy_179;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0172) 0))))
                    (show (nb068_alpha_dummy_177 f) ≠ (nb068_alpha_dummy_180 f) from (by
                        unfold nb068_alpha_dummy_180;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
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
                      ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
                      ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
                      ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
                      ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
                      ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                      ((nb068_alpha_dummy_001), x),
                      ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb068_split_alpha_0051 (x : Var) (y : Var) (f : Var) :
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
        ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
        ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
        ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
        ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
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
          ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
          ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
          ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
          ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
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

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
