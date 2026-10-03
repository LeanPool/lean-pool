/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C074C001Part006

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C074C001Part008`. -/


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
noncomputable def nb074_split_alpha_0003 (x : Var) :
    TAlphaWff
      [((nb074_alpha_dummy_046), (nb074_alpha_dummy_048 x)),
        ((nb074_alpha_dummy_045), (nb074_alpha_dummy_047 x)),
        ((nb074_alpha_dummy_075), (nb074_alpha_dummy_076 x)),
        ((nb074_alpha_dummy_049), (nb074_alpha_dummy_050 x)),
        ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)),
        ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)),
        ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)),
        ((nb074_alpha_dummy_000), x),
        ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
      (Wff.imp (Wff.classMem (Class.cv (nb074_alpha_dummy_046))
          (Class.cv (nb074_alpha_dummy_041))) (Wff.neg
          (Wff.classEq (Class.cv (nb074_alpha_dummy_045))
            (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_046))) (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb074_alpha_dummy_048 x))
          (Class.cv (nb074_alpha_dummy_043 x))) (Wff.neg
          (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x))
            (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_048 x))) (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_041) ≠ (nb074_alpha_dummy_046) from (by
              unfold nb074_alpha_dummy_046;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0072) 1))))
          (show (nb074_alpha_dummy_043 x) ≠ (nb074_alpha_dummy_048 x) from (by
              unfold nb074_alpha_dummy_048;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0074 x) 1))))
          (TAlphaVar.there (show (nb074_alpha_dummy_041) ≠ (nb074_alpha_dummy_045) from (by
                unfold nb074_alpha_dummy_045;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0072) 0))))
            (show (nb074_alpha_dummy_043 x) ≠ (nb074_alpha_dummy_047 x) from (by
                unfold nb074_alpha_dummy_047;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0074 x) 0))))
            (TAlphaVar.there (show (nb074_alpha_dummy_041) ≠ (nb074_alpha_dummy_075) from (by
                  unfold nb074_alpha_dummy_075;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0076) 0))))
              (show (nb074_alpha_dummy_043 x) ≠ (nb074_alpha_dummy_076 x) from (by
                  unfold nb074_alpha_dummy_076;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0077 x) 0))))
              (TAlphaVar.there (show (nb074_alpha_dummy_041) ≠ (nb074_alpha_dummy_049) from (by
                    unfold nb074_alpha_dummy_049;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0073) 0))))
                (show (nb074_alpha_dummy_043 x) ≠ (nb074_alpha_dummy_050 x) from (by
                    unfold nb074_alpha_dummy_050;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0075 x) 0))))
                (TAlphaVar.there (freshVar_injective
                    (((syn_ccnv (Class.cv (nb074_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv)
                    (by decide))
                  (freshVar_injective (((syn_ccnv (Class.cv x))).fv ∪ ((syn_cvv)).fv)
                    (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb074_alpha_dummy_042))).fv ∪
                ((Class.cv (nb074_alpha_dummy_041))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb074_alpha_dummy_044 x))).fv ∪
                ((Class.cv (nb074_alpha_dummy_043 x))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb074_alpha_dummy_046) ≠ (nb074_alpha_dummy_053) from (by
                                        unfold nb074_alpha_dummy_053;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0050)
                                                0)))) (show (nb074_alpha_dummy_048 x) ≠
                                        (nb074_alpha_dummy_055 x) from (by
                                        unfold nb074_alpha_dummy_055;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0051 x)
                                                0)))) (TAlphaVar.there (show
                                        (nb074_alpha_dummy_046) ≠ (nb074_alpha_dummy_054) from
                                        (by
                                          unfold nb074_alpha_dummy_054;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb074_support_mem_0050)
                                                  1)))) (show (nb074_alpha_dummy_048 x) ≠
        (nb074_alpha_dummy_056 x) from (by
                                          unfold nb074_alpha_dummy_056;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb074_support_mem_0051 x) 1))))
                                      (TAlphaVar.there (show (nb074_alpha_dummy_046) ≠
        (nb074_alpha_dummy_079) from (by
          unfold nb074_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0080) 0)))) (show (nb074_alpha_dummy_048 x) ≠
        (nb074_alpha_dummy_080 x) from (by
          unfold nb074_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0081 x) 0)))) (TAlphaVar.there (show
        (nb074_alpha_dummy_046) ≠ (nb074_alpha_dummy_077) from (by
          unfold nb074_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0078) 0)))) (show (nb074_alpha_dummy_048 x) ≠
        (nb074_alpha_dummy_078 x) from (by
          unfold nb074_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0079 x) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb074_alpha_dummy_046))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb074_alpha_dummy_048 x))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_053) ≠ (nb074_alpha_dummy_060) from (by
          unfold nb074_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0054)
                  1)))) (show (nb074_alpha_dummy_055 x) ≠ (nb074_alpha_dummy_063 x) from (by
          unfold nb074_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0055
                    x)
                  1)))) (TAlphaVar.there (show (nb074_alpha_dummy_053) ≠ (nb074_alpha_dummy_059)
        from (by
          unfold nb074_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0054)
                  0)))) (show (nb074_alpha_dummy_055 x) ≠ (nb074_alpha_dummy_062 x) from (by
          unfold nb074_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0055
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_053) ≠ (nb074_alpha_dummy_057)
        from (by
          unfold
            nb074_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0052)
                  0)))) (show (nb074_alpha_dummy_055 x) ≠ (nb074_alpha_dummy_058 x) from (by
          unfold
            nb074_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0053
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb074_alpha_dummy_061), (nb074_alpha_dummy_064 x)), ((nb074_alpha_dummy_060),
        (nb074_alpha_dummy_063 x)), ((nb074_alpha_dummy_059), (nb074_alpha_dummy_062 x)),
        ((nb074_alpha_dummy_057), (nb074_alpha_dummy_058 x)), ((nb074_alpha_dummy_053),
        (nb074_alpha_dummy_055 x)), ((nb074_alpha_dummy_054), (nb074_alpha_dummy_056 x)),
        ((nb074_alpha_dummy_079), (nb074_alpha_dummy_080 x)), ((nb074_alpha_dummy_077),
        (nb074_alpha_dummy_078 x)), ((nb074_alpha_dummy_046), (nb074_alpha_dummy_048 x)),
        ((nb074_alpha_dummy_045), (nb074_alpha_dummy_047 x)), ((nb074_alpha_dummy_075),
        (nb074_alpha_dummy_076 x)), ((nb074_alpha_dummy_049), (nb074_alpha_dummy_050 x)),
        ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041),
        (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)),
        ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_060) ≠ (nb074_alpha_dummy_067) from (by
          unfold
            nb074_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0058)
                  0)))) (show (nb074_alpha_dummy_063 x) ≠ (nb074_alpha_dummy_068 x) from (by
          unfold
            nb074_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0059
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_060) ≠ (nb074_alpha_dummy_065)
        from (by
          unfold
            nb074_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0056)
                  0)))) (show (nb074_alpha_dummy_063 x) ≠ (nb074_alpha_dummy_066 x) from (by
          unfold
            nb074_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0057
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_061) ≠
        (nb074_alpha_dummy_067) from (by
          unfold
            nb074_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0062)
                  0)))) (show (nb074_alpha_dummy_064 x) ≠ (nb074_alpha_dummy_068 x) from (by
          unfold
            nb074_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0063
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_061) ≠ (nb074_alpha_dummy_065)
        from (by
          unfold
            nb074_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0060)
                  0)))) (show (nb074_alpha_dummy_064 x) ≠ (nb074_alpha_dummy_066 x) from (by
          unfold
            nb074_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0061
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_060) ≠ (nb074_alpha_dummy_067) from (by
          unfold
            nb074_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0058)
                  0)))) (show (nb074_alpha_dummy_063 x) ≠ (nb074_alpha_dummy_068 x) from (by
          unfold
            nb074_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0059
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_060) ≠ (nb074_alpha_dummy_065)
        from (by
          unfold
            nb074_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0056)
                  0)))) (show (nb074_alpha_dummy_063 x) ≠ (nb074_alpha_dummy_066 x) from (by
          unfold
            nb074_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0057
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_061) ≠
        (nb074_alpha_dummy_067) from (by
          unfold
            nb074_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0062)
                  0)))) (show (nb074_alpha_dummy_064 x) ≠ (nb074_alpha_dummy_068 x) from (by
          unfold
            nb074_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0063
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_061) ≠ (nb074_alpha_dummy_065)
        from (by
          unfold
            nb074_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0060)
                  0)))) (show (nb074_alpha_dummy_064 x) ≠ (nb074_alpha_dummy_066 x) from (by
          unfold
            nb074_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0061
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb074_alpha_dummy_061), (nb074_alpha_dummy_064 x)), ((nb074_alpha_dummy_060),
        (nb074_alpha_dummy_063 x)), ((nb074_alpha_dummy_059), (nb074_alpha_dummy_062 x)),
        ((nb074_alpha_dummy_057), (nb074_alpha_dummy_058 x)), ((nb074_alpha_dummy_053),
        (nb074_alpha_dummy_055 x)), ((nb074_alpha_dummy_054), (nb074_alpha_dummy_056 x)),
        ((nb074_alpha_dummy_079), (nb074_alpha_dummy_080 x)), ((nb074_alpha_dummy_077),
        (nb074_alpha_dummy_078 x)), ((nb074_alpha_dummy_046), (nb074_alpha_dummy_048 x)),
        ((nb074_alpha_dummy_045), (nb074_alpha_dummy_047 x)), ((nb074_alpha_dummy_075),
        (nb074_alpha_dummy_076 x)), ((nb074_alpha_dummy_049), (nb074_alpha_dummy_050 x)),
        ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041),
        (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)),
        ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_053))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_055
        x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_060) ≠
        (nb074_alpha_dummy_071) from (by
          unfold
            nb074_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0066)
                  0)))) (show (nb074_alpha_dummy_063 x) ≠ (nb074_alpha_dummy_072 x) from (by
          unfold
            nb074_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_060) ≠ (nb074_alpha_dummy_069)
        from (by
          unfold
            nb074_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0064)
                  0)))) (show (nb074_alpha_dummy_063 x) ≠ (nb074_alpha_dummy_070 x) from (by
          unfold
            nb074_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_060) ≠
        (nb074_alpha_dummy_071) from (by
          unfold
            nb074_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0066)
                  0)))) (show (nb074_alpha_dummy_063 x) ≠ (nb074_alpha_dummy_072 x) from (by
          unfold
            nb074_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_060) ≠ (nb074_alpha_dummy_069)
        from (by
          unfold
            nb074_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0064)
                  0)))) (show (nb074_alpha_dummy_063 x) ≠ (nb074_alpha_dummy_070 x) from (by
          unfold
            nb074_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_061) ≠ (nb074_alpha_dummy_073) from (by
          unfold
            nb074_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0070)
                  0)))) (show (nb074_alpha_dummy_064 x) ≠ (nb074_alpha_dummy_074 x) from (by
          unfold
            nb074_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_061) ≠ (nb074_alpha_dummy_069)
        from (by
          unfold
            nb074_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0068)
                  0)))) (show (nb074_alpha_dummy_064 x) ≠ (nb074_alpha_dummy_070 x) from (by
          unfold
            nb074_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_061) ≠
        (nb074_alpha_dummy_073) from (by
          unfold
            nb074_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0070)
                  0)))) (show (nb074_alpha_dummy_064 x) ≠ (nb074_alpha_dummy_074 x) from (by
          unfold
            nb074_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_061) ≠ (nb074_alpha_dummy_069)
        from (by
          unfold
            nb074_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0068)
                  0)))) (show (nb074_alpha_dummy_064 x) ≠ (nb074_alpha_dummy_070 x) from (by
          unfold
            nb074_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_053) ≠ (nb074_alpha_dummy_057)
        from (by
          unfold nb074_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0052) 0)))) (show (nb074_alpha_dummy_055 x) ≠
        (nb074_alpha_dummy_058 x) from (by
          unfold nb074_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb074_alpha_dummy_057), (nb074_alpha_dummy_058 x)),
        ((nb074_alpha_dummy_053), (nb074_alpha_dummy_055 x)), ((nb074_alpha_dummy_054),
        (nb074_alpha_dummy_056 x)), ((nb074_alpha_dummy_079), (nb074_alpha_dummy_080 x)),
        ((nb074_alpha_dummy_077), (nb074_alpha_dummy_078 x)), ((nb074_alpha_dummy_046),
        (nb074_alpha_dummy_048 x)), ((nb074_alpha_dummy_045), (nb074_alpha_dummy_047 x)),
        ((nb074_alpha_dummy_075), (nb074_alpha_dummy_076 x)), ((nb074_alpha_dummy_049),
        (nb074_alpha_dummy_050 x)), ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)),
        ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001),
        (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003),
        (nb074_alpha_dummy_004 x))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_053) ≠ (nb074_alpha_dummy_057) from (by
          unfold nb074_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0052) 0)))) (show (nb074_alpha_dummy_055 x) ≠
        (nb074_alpha_dummy_058 x) from (by
          unfold nb074_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb074_alpha_dummy_053) ≠ (nb074_alpha_dummy_057) from (by
          unfold nb074_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0052) 0)))) (show (nb074_alpha_dummy_055 x) ≠
        (nb074_alpha_dummy_058 x) from (by
          unfold nb074_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb074_alpha_dummy_057), (nb074_alpha_dummy_058 x)),
        ((nb074_alpha_dummy_053), (nb074_alpha_dummy_055 x)), ((nb074_alpha_dummy_054),
        (nb074_alpha_dummy_056 x)), ((nb074_alpha_dummy_079), (nb074_alpha_dummy_080 x)),
        ((nb074_alpha_dummy_077), (nb074_alpha_dummy_078 x)), ((nb074_alpha_dummy_046),
        (nb074_alpha_dummy_048 x)), ((nb074_alpha_dummy_045), (nb074_alpha_dummy_047 x)),
        ((nb074_alpha_dummy_075), (nb074_alpha_dummy_076 x)), ((nb074_alpha_dummy_049),
        (nb074_alpha_dummy_050 x)), ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)),
        ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001),
        (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003),
        (nb074_alpha_dummy_004 x))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb074_alpha_dummy_046) ≠ (nb074_alpha_dummy_053) from (by
                                        unfold nb074_alpha_dummy_053;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0050)
                                                0)))) (show (nb074_alpha_dummy_048 x) ≠
                                        (nb074_alpha_dummy_055 x) from (by
                                        unfold nb074_alpha_dummy_055;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0051 x)
                                                0)))) (TAlphaVar.there (show
                                        (nb074_alpha_dummy_046) ≠ (nb074_alpha_dummy_054) from
                                        (by
                                          unfold nb074_alpha_dummy_054;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb074_support_mem_0050)
                                                  1)))) (show (nb074_alpha_dummy_048 x) ≠
        (nb074_alpha_dummy_056 x) from (by
                                          unfold nb074_alpha_dummy_056;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb074_support_mem_0051 x) 1))))
                                      (TAlphaVar.there (show (nb074_alpha_dummy_046) ≠
        (nb074_alpha_dummy_079) from (by
          unfold nb074_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0080) 0)))) (show (nb074_alpha_dummy_048 x) ≠
        (nb074_alpha_dummy_080 x) from (by
          unfold nb074_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0081 x) 0)))) (TAlphaVar.there (show
        (nb074_alpha_dummy_046) ≠ (nb074_alpha_dummy_077) from (by
          unfold nb074_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0078) 0)))) (show (nb074_alpha_dummy_048 x) ≠
        (nb074_alpha_dummy_078 x) from (by
          unfold nb074_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0079 x) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb074_alpha_dummy_046))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb074_alpha_dummy_048 x))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_053) ≠ (nb074_alpha_dummy_060) from (by
          unfold nb074_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0054)
                  1)))) (show (nb074_alpha_dummy_055 x) ≠ (nb074_alpha_dummy_063 x) from (by
          unfold nb074_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0055
                    x)
                  1)))) (TAlphaVar.there (show (nb074_alpha_dummy_053) ≠ (nb074_alpha_dummy_059)
        from (by
          unfold nb074_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0054)
                  0)))) (show (nb074_alpha_dummy_055 x) ≠ (nb074_alpha_dummy_062 x) from (by
          unfold nb074_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0055
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_053) ≠ (nb074_alpha_dummy_057)
        from (by
          unfold
            nb074_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0052)
                  0)))) (show (nb074_alpha_dummy_055 x) ≠ (nb074_alpha_dummy_058 x) from (by
          unfold
            nb074_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0053
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb074_alpha_dummy_061), (nb074_alpha_dummy_064 x)), ((nb074_alpha_dummy_060),
        (nb074_alpha_dummy_063 x)), ((nb074_alpha_dummy_059), (nb074_alpha_dummy_062 x)),
        ((nb074_alpha_dummy_057), (nb074_alpha_dummy_058 x)), ((nb074_alpha_dummy_053),
        (nb074_alpha_dummy_055 x)), ((nb074_alpha_dummy_054), (nb074_alpha_dummy_056 x)),
        ((nb074_alpha_dummy_079), (nb074_alpha_dummy_080 x)), ((nb074_alpha_dummy_077),
        (nb074_alpha_dummy_078 x)), ((nb074_alpha_dummy_046), (nb074_alpha_dummy_048 x)),
        ((nb074_alpha_dummy_045), (nb074_alpha_dummy_047 x)), ((nb074_alpha_dummy_075),
        (nb074_alpha_dummy_076 x)), ((nb074_alpha_dummy_049), (nb074_alpha_dummy_050 x)),
        ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041),
        (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)),
        ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_060) ≠ (nb074_alpha_dummy_067) from (by
          unfold
            nb074_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0058)
                  0)))) (show (nb074_alpha_dummy_063 x) ≠ (nb074_alpha_dummy_068 x) from (by
          unfold
            nb074_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0059
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_060) ≠ (nb074_alpha_dummy_065)
        from (by
          unfold
            nb074_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0056)
                  0)))) (show (nb074_alpha_dummy_063 x) ≠ (nb074_alpha_dummy_066 x) from (by
          unfold
            nb074_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0057
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_061) ≠
        (nb074_alpha_dummy_067) from (by
          unfold
            nb074_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0062)
                  0)))) (show (nb074_alpha_dummy_064 x) ≠ (nb074_alpha_dummy_068 x) from (by
          unfold
            nb074_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0063
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_061) ≠ (nb074_alpha_dummy_065)
        from (by
          unfold
            nb074_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0060)
                  0)))) (show (nb074_alpha_dummy_064 x) ≠ (nb074_alpha_dummy_066 x) from (by
          unfold
            nb074_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0061
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_060) ≠ (nb074_alpha_dummy_067) from (by
          unfold
            nb074_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0058)
                  0)))) (show (nb074_alpha_dummy_063 x) ≠ (nb074_alpha_dummy_068 x) from (by
          unfold
            nb074_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0059
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_060) ≠ (nb074_alpha_dummy_065)
        from (by
          unfold
            nb074_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0056)
                  0)))) (show (nb074_alpha_dummy_063 x) ≠ (nb074_alpha_dummy_066 x) from (by
          unfold
            nb074_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0057
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_061) ≠
        (nb074_alpha_dummy_067) from (by
          unfold
            nb074_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0062)
                  0)))) (show (nb074_alpha_dummy_064 x) ≠ (nb074_alpha_dummy_068 x) from (by
          unfold
            nb074_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0063
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_061) ≠ (nb074_alpha_dummy_065)
        from (by
          unfold
            nb074_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0060)
                  0)))) (show (nb074_alpha_dummy_064 x) ≠ (nb074_alpha_dummy_066 x) from (by
          unfold
            nb074_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0061
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb074_alpha_dummy_061), (nb074_alpha_dummy_064 x)), ((nb074_alpha_dummy_060),
        (nb074_alpha_dummy_063 x)), ((nb074_alpha_dummy_059), (nb074_alpha_dummy_062 x)),
        ((nb074_alpha_dummy_057), (nb074_alpha_dummy_058 x)), ((nb074_alpha_dummy_053),
        (nb074_alpha_dummy_055 x)), ((nb074_alpha_dummy_054), (nb074_alpha_dummy_056 x)),
        ((nb074_alpha_dummy_079), (nb074_alpha_dummy_080 x)), ((nb074_alpha_dummy_077),
        (nb074_alpha_dummy_078 x)), ((nb074_alpha_dummy_046), (nb074_alpha_dummy_048 x)),
        ((nb074_alpha_dummy_045), (nb074_alpha_dummy_047 x)), ((nb074_alpha_dummy_075),
        (nb074_alpha_dummy_076 x)), ((nb074_alpha_dummy_049), (nb074_alpha_dummy_050 x)),
        ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041),
        (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)),
        ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_053))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_055
        x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_060) ≠
        (nb074_alpha_dummy_071) from (by
          unfold
            nb074_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0066)
                  0)))) (show (nb074_alpha_dummy_063 x) ≠ (nb074_alpha_dummy_072 x) from (by
          unfold
            nb074_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_060) ≠ (nb074_alpha_dummy_069)
        from (by
          unfold
            nb074_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0064)
                  0)))) (show (nb074_alpha_dummy_063 x) ≠ (nb074_alpha_dummy_070 x) from (by
          unfold
            nb074_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_060) ≠
        (nb074_alpha_dummy_071) from (by
          unfold
            nb074_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0066)
                  0)))) (show (nb074_alpha_dummy_063 x) ≠ (nb074_alpha_dummy_072 x) from (by
          unfold
            nb074_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_060) ≠ (nb074_alpha_dummy_069)
        from (by
          unfold
            nb074_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0064)
                  0)))) (show (nb074_alpha_dummy_063 x) ≠ (nb074_alpha_dummy_070 x) from (by
          unfold
            nb074_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_061) ≠ (nb074_alpha_dummy_073) from (by
          unfold
            nb074_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0070)
                  0)))) (show (nb074_alpha_dummy_064 x) ≠ (nb074_alpha_dummy_074 x) from (by
          unfold
            nb074_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_061) ≠ (nb074_alpha_dummy_069)
        from (by
          unfold
            nb074_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0068)
                  0)))) (show (nb074_alpha_dummy_064 x) ≠ (nb074_alpha_dummy_070 x) from (by
          unfold
            nb074_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_061) ≠
        (nb074_alpha_dummy_073) from (by
          unfold
            nb074_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0070)
                  0)))) (show (nb074_alpha_dummy_064 x) ≠ (nb074_alpha_dummy_074 x) from (by
          unfold
            nb074_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_061) ≠ (nb074_alpha_dummy_069)
        from (by
          unfold
            nb074_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0068)
                  0)))) (show (nb074_alpha_dummy_064 x) ≠ (nb074_alpha_dummy_070 x) from (by
          unfold
            nb074_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_053) ≠ (nb074_alpha_dummy_057)
        from (by
          unfold nb074_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0052) 0)))) (show (nb074_alpha_dummy_055 x) ≠
        (nb074_alpha_dummy_058 x) from (by
          unfold nb074_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb074_alpha_dummy_057), (nb074_alpha_dummy_058 x)),
        ((nb074_alpha_dummy_053), (nb074_alpha_dummy_055 x)), ((nb074_alpha_dummy_054),
        (nb074_alpha_dummy_056 x)), ((nb074_alpha_dummy_079), (nb074_alpha_dummy_080 x)),
        ((nb074_alpha_dummy_077), (nb074_alpha_dummy_078 x)), ((nb074_alpha_dummy_046),
        (nb074_alpha_dummy_048 x)), ((nb074_alpha_dummy_045), (nb074_alpha_dummy_047 x)),
        ((nb074_alpha_dummy_075), (nb074_alpha_dummy_076 x)), ((nb074_alpha_dummy_049),
        (nb074_alpha_dummy_050 x)), ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)),
        ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001),
        (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003),
        (nb074_alpha_dummy_004 x))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_053) ≠ (nb074_alpha_dummy_057) from (by
          unfold nb074_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0052) 0)))) (show (nb074_alpha_dummy_055 x) ≠
        (nb074_alpha_dummy_058 x) from (by
          unfold nb074_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb074_alpha_dummy_053) ≠ (nb074_alpha_dummy_057) from (by
          unfold nb074_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0052) 0)))) (show (nb074_alpha_dummy_055 x) ≠
        (nb074_alpha_dummy_058 x) from (by
          unfold nb074_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb074_alpha_dummy_057), (nb074_alpha_dummy_058 x)),
        ((nb074_alpha_dummy_053), (nb074_alpha_dummy_055 x)), ((nb074_alpha_dummy_054),
        (nb074_alpha_dummy_056 x)), ((nb074_alpha_dummy_079), (nb074_alpha_dummy_080 x)),
        ((nb074_alpha_dummy_077), (nb074_alpha_dummy_078 x)), ((nb074_alpha_dummy_046),
        (nb074_alpha_dummy_048 x)), ((nb074_alpha_dummy_045), (nb074_alpha_dummy_047 x)),
        ((nb074_alpha_dummy_075), (nb074_alpha_dummy_076 x)), ((nb074_alpha_dummy_049),
        (nb074_alpha_dummy_050 x)), ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)),
        ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001),
        (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003),
        (nb074_alpha_dummy_004 x))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb074_alpha_dummy_077), (nb074_alpha_dummy_078 x)),
                    ((nb074_alpha_dummy_046), (nb074_alpha_dummy_048 x)),
                    ((nb074_alpha_dummy_045), (nb074_alpha_dummy_047 x)),
                    ((nb074_alpha_dummy_075), (nb074_alpha_dummy_076 x)),
                    ((nb074_alpha_dummy_049), (nb074_alpha_dummy_050 x)),
                    ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)),
                    ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)),
                    ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)),
                    ((nb074_alpha_dummy_000), x),
                    ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
                  (syn_ccompl (syn_csn (syn_c0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

@[expose]
noncomputable def nb074_split_alpha_0004 (x : Var) :
    TAlphaWff
      [((nb074_alpha_dummy_049), (nb074_alpha_dummy_050 x)),
        ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)),
        ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)),
        ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)),
        ((nb074_alpha_dummy_000), x),
        ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
      (Wff.imp (Wff.classMem (Class.cv (nb074_alpha_dummy_049)) (syn_ccompl
            (Class.cab (nb074_alpha_dummy_045)
              (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_042))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_045))
                  (syn_cphi (Class.cv (nb074_alpha_dummy_046)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb074_alpha_dummy_049)) (syn_ccompl
              (Class.cab (nb074_alpha_dummy_045)
                (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_041))
                  (Wff.classEq (Class.cv (nb074_alpha_dummy_045))
                    (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_046)))
                      (syn_csn (syn_c0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb074_alpha_dummy_050 x)) (syn_ccompl
            (Class.cab (nb074_alpha_dummy_047 x)
              (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_044 x))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x))
                  (syn_cphi (Class.cv (nb074_alpha_dummy_048 x)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb074_alpha_dummy_050 x)) (syn_ccompl
              (Class.cab (nb074_alpha_dummy_047 x)
                (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_043 x))
                  (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x))
                    (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_048 x)))
                      (syn_csn (syn_c0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb074_alpha_dummy_042) ≠ (nb074_alpha_dummy_046) from (by
                              unfold nb074_alpha_dummy_046;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb074_support_mem_0044) 1))))
                          (show (nb074_alpha_dummy_044 x) ≠ (nb074_alpha_dummy_048 x) from (by
                              unfold nb074_alpha_dummy_048;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb074_support_mem_0046 x) 1))))
                          (TAlphaVar.there
                            (show (nb074_alpha_dummy_042) ≠ (nb074_alpha_dummy_045) from (by
                                unfold nb074_alpha_dummy_045;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb074_support_mem_0044) 0))))
                            (show (nb074_alpha_dummy_044 x) ≠ (nb074_alpha_dummy_047 x) from (by
                                unfold nb074_alpha_dummy_047;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb074_support_mem_0046 x) 0))))
                            (TAlphaVar.there
                              (show (nb074_alpha_dummy_042) ≠ (nb074_alpha_dummy_051) from (by
                                  unfold nb074_alpha_dummy_051;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb074_support_mem_0048) 0))))
                              (show (nb074_alpha_dummy_044 x) ≠ (nb074_alpha_dummy_052 x) from
                                (by
                                  unfold nb074_alpha_dummy_052;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb074_support_mem_0049 x) 0))))
                              (TAlphaVar.there
                                (show (nb074_alpha_dummy_042) ≠ (nb074_alpha_dummy_049) from (by
                                    unfold nb074_alpha_dummy_049;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb074_support_mem_0045) 0)))) (show
                                  (nb074_alpha_dummy_044 x) ≠ (nb074_alpha_dummy_050 x) from (by
                                    unfold nb074_alpha_dummy_050;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb074_support_mem_0047 x)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb074_alpha_dummy_042))).fv ∪
                              ((Class.cv (nb074_alpha_dummy_041))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb074_alpha_dummy_044 x))).fv ∪
                              ((Class.cv (nb074_alpha_dummy_043 x))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb074_alpha_dummy_046) ≠ (nb074_alpha_dummy_053) from
                                    (by
                                      unfold nb074_alpha_dummy_053;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb074_support_mem_0050)
                                              0)))) (show
                                    (nb074_alpha_dummy_048 x) ≠ (nb074_alpha_dummy_055 x) from
                                    (by
                                      unfold nb074_alpha_dummy_055;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb074_support_mem_0051 x)
                                              0)))) (TAlphaVar.there (show
                                      (nb074_alpha_dummy_046) ≠ (nb074_alpha_dummy_054) from (by
                                        unfold nb074_alpha_dummy_054;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0050)
                                                1)))) (show (nb074_alpha_dummy_048 x) ≠
                                        (nb074_alpha_dummy_056 x) from (by
                                        unfold nb074_alpha_dummy_056;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0051 x)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb074_alpha_dummy_046))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb074_alpha_dummy_048 x))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb074_alpha_dummy_053) ≠ (nb074_alpha_dummy_060) from (by
          unfold nb074_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0054)
                  1)))) (show (nb074_alpha_dummy_055 x) ≠ (nb074_alpha_dummy_063 x) from (by
          unfold nb074_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0055 x)
                  1)))) (TAlphaVar.there (show (nb074_alpha_dummy_053) ≠ (nb074_alpha_dummy_059)
        from (by
          unfold nb074_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0054)
                  0)))) (show (nb074_alpha_dummy_055 x) ≠ (nb074_alpha_dummy_062 x) from (by
          unfold nb074_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0055
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_053) ≠ (nb074_alpha_dummy_057)
        from (by
          unfold nb074_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0052)
                  0)))) (show (nb074_alpha_dummy_055 x) ≠ (nb074_alpha_dummy_058 x) from (by
          unfold nb074_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0053
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb074_alpha_dummy_061), (nb074_alpha_dummy_064 x)), ((nb074_alpha_dummy_060),
        (nb074_alpha_dummy_063 x)), ((nb074_alpha_dummy_059), (nb074_alpha_dummy_062 x)),
        ((nb074_alpha_dummy_057), (nb074_alpha_dummy_058 x)), ((nb074_alpha_dummy_053),
        (nb074_alpha_dummy_055 x)), ((nb074_alpha_dummy_054), (nb074_alpha_dummy_056 x)),
        ((nb074_alpha_dummy_046), (nb074_alpha_dummy_048 x)), ((nb074_alpha_dummy_045),
        (nb074_alpha_dummy_047 x)), ((nb074_alpha_dummy_051), (nb074_alpha_dummy_052 x)),
        ((nb074_alpha_dummy_049), (nb074_alpha_dummy_050 x)), ((nb074_alpha_dummy_042),
        (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)),
        ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x),
        ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] (syn_c1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_060) ≠ (nb074_alpha_dummy_067) from (by
          unfold
            nb074_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0058)
                  0)))) (show (nb074_alpha_dummy_063 x) ≠ (nb074_alpha_dummy_068 x) from (by
          unfold
            nb074_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0059
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_060) ≠ (nb074_alpha_dummy_065)
        from (by
          unfold
            nb074_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0056)
                  0)))) (show (nb074_alpha_dummy_063 x) ≠ (nb074_alpha_dummy_066 x) from (by
          unfold
            nb074_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0057
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_061) ≠
        (nb074_alpha_dummy_067) from (by
          unfold
            nb074_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0062)
                  0)))) (show (nb074_alpha_dummy_064 x) ≠ (nb074_alpha_dummy_068 x) from (by
          unfold
            nb074_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0063
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_061) ≠ (nb074_alpha_dummy_065)
        from (by
          unfold
            nb074_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0060)
                  0)))) (show (nb074_alpha_dummy_064 x) ≠ (nb074_alpha_dummy_066 x) from (by
          unfold
            nb074_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0061
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_060) ≠ (nb074_alpha_dummy_067) from (by
          unfold
            nb074_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0058)
                  0)))) (show (nb074_alpha_dummy_063 x) ≠ (nb074_alpha_dummy_068 x) from (by
          unfold
            nb074_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0059
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_060) ≠ (nb074_alpha_dummy_065)
        from (by
          unfold
            nb074_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0056)
                  0)))) (show (nb074_alpha_dummy_063 x) ≠ (nb074_alpha_dummy_066 x) from (by
          unfold
            nb074_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0057
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_061) ≠
        (nb074_alpha_dummy_067) from (by
          unfold
            nb074_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0062)
                  0)))) (show (nb074_alpha_dummy_064 x) ≠ (nb074_alpha_dummy_068 x) from (by
          unfold
            nb074_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0063
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_061) ≠ (nb074_alpha_dummy_065)
        from (by
          unfold
            nb074_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0060)
                  0)))) (show (nb074_alpha_dummy_064 x) ≠ (nb074_alpha_dummy_066 x) from (by
          unfold
            nb074_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0061
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb074_alpha_dummy_061), (nb074_alpha_dummy_064 x)), ((nb074_alpha_dummy_060),
        (nb074_alpha_dummy_063 x)), ((nb074_alpha_dummy_059), (nb074_alpha_dummy_062 x)),
        ((nb074_alpha_dummy_057), (nb074_alpha_dummy_058 x)), ((nb074_alpha_dummy_053),
        (nb074_alpha_dummy_055 x)), ((nb074_alpha_dummy_054), (nb074_alpha_dummy_056 x)),
        ((nb074_alpha_dummy_046), (nb074_alpha_dummy_048 x)), ((nb074_alpha_dummy_045),
        (nb074_alpha_dummy_047 x)), ((nb074_alpha_dummy_051), (nb074_alpha_dummy_052 x)),
        ((nb074_alpha_dummy_049), (nb074_alpha_dummy_050 x)), ((nb074_alpha_dummy_042),
        (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)),
        ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x),
        ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] (syn_c0)
        (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_060) ≠
        (nb074_alpha_dummy_071) from (by
          unfold
            nb074_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0066)
                  0)))) (show (nb074_alpha_dummy_063 x) ≠ (nb074_alpha_dummy_072 x) from (by
          unfold
            nb074_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_060) ≠ (nb074_alpha_dummy_069)
        from (by
          unfold
            nb074_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0064)
                  0)))) (show (nb074_alpha_dummy_063 x) ≠ (nb074_alpha_dummy_070 x) from (by
          unfold
            nb074_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_060) ≠
        (nb074_alpha_dummy_071) from (by
          unfold
            nb074_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0066)
                  0)))) (show (nb074_alpha_dummy_063 x) ≠ (nb074_alpha_dummy_072 x) from (by
          unfold
            nb074_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_060) ≠ (nb074_alpha_dummy_069)
        from (by
          unfold
            nb074_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0064)
                  0)))) (show (nb074_alpha_dummy_063 x) ≠ (nb074_alpha_dummy_070 x) from (by
          unfold
            nb074_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_061) ≠ (nb074_alpha_dummy_073) from (by
          unfold
            nb074_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0070)
                  0)))) (show (nb074_alpha_dummy_064 x) ≠ (nb074_alpha_dummy_074 x) from (by
          unfold
            nb074_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_061) ≠ (nb074_alpha_dummy_069)
        from (by
          unfold
            nb074_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0068)
                  0)))) (show (nb074_alpha_dummy_064 x) ≠ (nb074_alpha_dummy_070 x) from (by
          unfold
            nb074_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_061) ≠
        (nb074_alpha_dummy_073) from (by
          unfold
            nb074_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0070)
                  0)))) (show (nb074_alpha_dummy_064 x) ≠ (nb074_alpha_dummy_074 x) from (by
          unfold
            nb074_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_061) ≠ (nb074_alpha_dummy_069)
        from (by
          unfold
            nb074_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0068)
                  0)))) (show (nb074_alpha_dummy_064 x) ≠ (nb074_alpha_dummy_070 x) from (by
          unfold
            nb074_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb074_alpha_dummy_053) ≠ (nb074_alpha_dummy_057) from (by
          unfold nb074_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0052) 0)))) (show (nb074_alpha_dummy_055 x) ≠
        (nb074_alpha_dummy_058 x) from (by
          unfold nb074_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed [((nb074_alpha_dummy_057),
        (nb074_alpha_dummy_058 x)), ((nb074_alpha_dummy_053), (nb074_alpha_dummy_055 x)),
        ((nb074_alpha_dummy_054), (nb074_alpha_dummy_056 x)), ((nb074_alpha_dummy_046),
        (nb074_alpha_dummy_048 x)), ((nb074_alpha_dummy_045), (nb074_alpha_dummy_047 x)),
        ((nb074_alpha_dummy_051), (nb074_alpha_dummy_052 x)), ((nb074_alpha_dummy_049),
        (nb074_alpha_dummy_050 x)), ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)),
        ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001),
        (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003),
        (nb074_alpha_dummy_004 x))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cv (TAlphaVar.there (show
        (nb074_alpha_dummy_053) ≠ (nb074_alpha_dummy_057) from (by
          unfold nb074_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0052) 0)))) (show (nb074_alpha_dummy_055 x) ≠
        (nb074_alpha_dummy_058 x) from (by
          unfold nb074_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb074_alpha_dummy_053) ≠ (nb074_alpha_dummy_057) from (by
          unfold nb074_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0052) 0)))) (show (nb074_alpha_dummy_055 x) ≠
        (nb074_alpha_dummy_058 x) from (by
          unfold nb074_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed [((nb074_alpha_dummy_057),
        (nb074_alpha_dummy_058 x)), ((nb074_alpha_dummy_053), (nb074_alpha_dummy_055 x)),
        ((nb074_alpha_dummy_054), (nb074_alpha_dummy_056 x)), ((nb074_alpha_dummy_046),
        (nb074_alpha_dummy_048 x)), ((nb074_alpha_dummy_045), (nb074_alpha_dummy_047 x)),
        ((nb074_alpha_dummy_051), (nb074_alpha_dummy_052 x)), ((nb074_alpha_dummy_049),
        (nb074_alpha_dummy_050 x)), ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)),
        ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001),
        (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003),
        (nb074_alpha_dummy_004 x))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb074_alpha_dummy_042) ≠ (nb074_alpha_dummy_046) from (by
                              unfold nb074_alpha_dummy_046;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb074_support_mem_0044) 1))))
                          (show (nb074_alpha_dummy_044 x) ≠ (nb074_alpha_dummy_048 x) from (by
                              unfold nb074_alpha_dummy_048;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb074_support_mem_0046 x) 1))))
                          (TAlphaVar.there
                            (show (nb074_alpha_dummy_042) ≠ (nb074_alpha_dummy_045) from (by
                                unfold nb074_alpha_dummy_045;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb074_support_mem_0044) 0))))
                            (show (nb074_alpha_dummy_044 x) ≠ (nb074_alpha_dummy_047 x) from (by
                                unfold nb074_alpha_dummy_047;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb074_support_mem_0046 x) 0))))
                            (TAlphaVar.there
                              (show (nb074_alpha_dummy_042) ≠ (nb074_alpha_dummy_051) from (by
                                  unfold nb074_alpha_dummy_051;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb074_support_mem_0048) 0))))
                              (show (nb074_alpha_dummy_044 x) ≠ (nb074_alpha_dummy_052 x) from
                                (by
                                  unfold nb074_alpha_dummy_052;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb074_support_mem_0049 x) 0))))
                              (TAlphaVar.there
                                (show (nb074_alpha_dummy_042) ≠ (nb074_alpha_dummy_049) from (by
                                    unfold nb074_alpha_dummy_049;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb074_support_mem_0045) 0)))) (show
                                  (nb074_alpha_dummy_044 x) ≠ (nb074_alpha_dummy_050 x) from (by
                                    unfold nb074_alpha_dummy_050;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb074_support_mem_0047 x)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb074_alpha_dummy_042))).fv ∪
                              ((Class.cv (nb074_alpha_dummy_041))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb074_alpha_dummy_044 x))).fv ∪
                              ((Class.cv (nb074_alpha_dummy_043 x))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb074_alpha_dummy_046) ≠ (nb074_alpha_dummy_053) from
                                    (by
                                      unfold nb074_alpha_dummy_053;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb074_support_mem_0050)
                                              0)))) (show
                                    (nb074_alpha_dummy_048 x) ≠ (nb074_alpha_dummy_055 x) from
                                    (by
                                      unfold nb074_alpha_dummy_055;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb074_support_mem_0051 x)
                                              0)))) (TAlphaVar.there (show
                                      (nb074_alpha_dummy_046) ≠ (nb074_alpha_dummy_054) from (by
                                        unfold nb074_alpha_dummy_054;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0050)
                                                1)))) (show (nb074_alpha_dummy_048 x) ≠
                                        (nb074_alpha_dummy_056 x) from (by
                                        unfold nb074_alpha_dummy_056;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0051 x)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb074_alpha_dummy_046))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb074_alpha_dummy_048 x))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb074_alpha_dummy_053) ≠ (nb074_alpha_dummy_060) from (by
          unfold nb074_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0054)
                  1)))) (show (nb074_alpha_dummy_055 x) ≠ (nb074_alpha_dummy_063 x) from (by
          unfold nb074_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0055 x)
                  1)))) (TAlphaVar.there (show (nb074_alpha_dummy_053) ≠ (nb074_alpha_dummy_059)
        from (by
          unfold nb074_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0054)
                  0)))) (show (nb074_alpha_dummy_055 x) ≠ (nb074_alpha_dummy_062 x) from (by
          unfold nb074_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0055
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_053) ≠ (nb074_alpha_dummy_057)
        from (by
          unfold nb074_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0052)
                  0)))) (show (nb074_alpha_dummy_055 x) ≠ (nb074_alpha_dummy_058 x) from (by
          unfold nb074_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0053
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb074_alpha_dummy_061), (nb074_alpha_dummy_064 x)), ((nb074_alpha_dummy_060),
        (nb074_alpha_dummy_063 x)), ((nb074_alpha_dummy_059), (nb074_alpha_dummy_062 x)),
        ((nb074_alpha_dummy_057), (nb074_alpha_dummy_058 x)), ((nb074_alpha_dummy_053),
        (nb074_alpha_dummy_055 x)), ((nb074_alpha_dummy_054), (nb074_alpha_dummy_056 x)),
        ((nb074_alpha_dummy_046), (nb074_alpha_dummy_048 x)), ((nb074_alpha_dummy_045),
        (nb074_alpha_dummy_047 x)), ((nb074_alpha_dummy_051), (nb074_alpha_dummy_052 x)),
        ((nb074_alpha_dummy_049), (nb074_alpha_dummy_050 x)), ((nb074_alpha_dummy_042),
        (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)),
        ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x),
        ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] (syn_c1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_060) ≠ (nb074_alpha_dummy_067) from (by
          unfold
            nb074_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0058)
                  0)))) (show (nb074_alpha_dummy_063 x) ≠ (nb074_alpha_dummy_068 x) from (by
          unfold
            nb074_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0059
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_060) ≠ (nb074_alpha_dummy_065)
        from (by
          unfold
            nb074_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0056)
                  0)))) (show (nb074_alpha_dummy_063 x) ≠ (nb074_alpha_dummy_066 x) from (by
          unfold
            nb074_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0057
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_061) ≠
        (nb074_alpha_dummy_067) from (by
          unfold
            nb074_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0062)
                  0)))) (show (nb074_alpha_dummy_064 x) ≠ (nb074_alpha_dummy_068 x) from (by
          unfold
            nb074_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0063
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_061) ≠ (nb074_alpha_dummy_065)
        from (by
          unfold
            nb074_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0060)
                  0)))) (show (nb074_alpha_dummy_064 x) ≠ (nb074_alpha_dummy_066 x) from (by
          unfold
            nb074_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0061
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_060) ≠ (nb074_alpha_dummy_067) from (by
          unfold
            nb074_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0058)
                  0)))) (show (nb074_alpha_dummy_063 x) ≠ (nb074_alpha_dummy_068 x) from (by
          unfold
            nb074_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0059
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_060) ≠ (nb074_alpha_dummy_065)
        from (by
          unfold
            nb074_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0056)
                  0)))) (show (nb074_alpha_dummy_063 x) ≠ (nb074_alpha_dummy_066 x) from (by
          unfold
            nb074_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0057
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_061) ≠
        (nb074_alpha_dummy_067) from (by
          unfold
            nb074_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0062)
                  0)))) (show (nb074_alpha_dummy_064 x) ≠ (nb074_alpha_dummy_068 x) from (by
          unfold
            nb074_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0063
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_061) ≠ (nb074_alpha_dummy_065)
        from (by
          unfold
            nb074_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0060)
                  0)))) (show (nb074_alpha_dummy_064 x) ≠ (nb074_alpha_dummy_066 x) from (by
          unfold
            nb074_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0061
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb074_alpha_dummy_061), (nb074_alpha_dummy_064 x)), ((nb074_alpha_dummy_060),
        (nb074_alpha_dummy_063 x)), ((nb074_alpha_dummy_059), (nb074_alpha_dummy_062 x)),
        ((nb074_alpha_dummy_057), (nb074_alpha_dummy_058 x)), ((nb074_alpha_dummy_053),
        (nb074_alpha_dummy_055 x)), ((nb074_alpha_dummy_054), (nb074_alpha_dummy_056 x)),
        ((nb074_alpha_dummy_046), (nb074_alpha_dummy_048 x)), ((nb074_alpha_dummy_045),
        (nb074_alpha_dummy_047 x)), ((nb074_alpha_dummy_051), (nb074_alpha_dummy_052 x)),
        ((nb074_alpha_dummy_049), (nb074_alpha_dummy_050 x)), ((nb074_alpha_dummy_042),
        (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)),
        ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x),
        ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] (syn_c0)
        (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_060) ≠
        (nb074_alpha_dummy_071) from (by
          unfold
            nb074_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0066)
                  0)))) (show (nb074_alpha_dummy_063 x) ≠ (nb074_alpha_dummy_072 x) from (by
          unfold
            nb074_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_060) ≠ (nb074_alpha_dummy_069)
        from (by
          unfold
            nb074_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0064)
                  0)))) (show (nb074_alpha_dummy_063 x) ≠ (nb074_alpha_dummy_070 x) from (by
          unfold
            nb074_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_060) ≠
        (nb074_alpha_dummy_071) from (by
          unfold
            nb074_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0066)
                  0)))) (show (nb074_alpha_dummy_063 x) ≠ (nb074_alpha_dummy_072 x) from (by
          unfold
            nb074_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_060) ≠ (nb074_alpha_dummy_069)
        from (by
          unfold
            nb074_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0064)
                  0)))) (show (nb074_alpha_dummy_063 x) ≠ (nb074_alpha_dummy_070 x) from (by
          unfold
            nb074_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_055 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_061) ≠ (nb074_alpha_dummy_073) from (by
          unfold
            nb074_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0070)
                  0)))) (show (nb074_alpha_dummy_064 x) ≠ (nb074_alpha_dummy_074 x) from (by
          unfold
            nb074_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_061) ≠ (nb074_alpha_dummy_069)
        from (by
          unfold
            nb074_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0068)
                  0)))) (show (nb074_alpha_dummy_064 x) ≠ (nb074_alpha_dummy_070 x) from (by
          unfold
            nb074_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_061) ≠
        (nb074_alpha_dummy_073) from (by
          unfold
            nb074_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0070)
                  0)))) (show (nb074_alpha_dummy_064 x) ≠ (nb074_alpha_dummy_074 x) from (by
          unfold
            nb074_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_061) ≠ (nb074_alpha_dummy_069)
        from (by
          unfold
            nb074_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0068)
                  0)))) (show (nb074_alpha_dummy_064 x) ≠ (nb074_alpha_dummy_070 x) from (by
          unfold
            nb074_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb074_alpha_dummy_053) ≠ (nb074_alpha_dummy_057) from (by
          unfold nb074_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0052) 0)))) (show (nb074_alpha_dummy_055 x) ≠
        (nb074_alpha_dummy_058 x) from (by
          unfold nb074_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed [((nb074_alpha_dummy_057),
        (nb074_alpha_dummy_058 x)), ((nb074_alpha_dummy_053), (nb074_alpha_dummy_055 x)),
        ((nb074_alpha_dummy_054), (nb074_alpha_dummy_056 x)), ((nb074_alpha_dummy_046),
        (nb074_alpha_dummy_048 x)), ((nb074_alpha_dummy_045), (nb074_alpha_dummy_047 x)),
        ((nb074_alpha_dummy_051), (nb074_alpha_dummy_052 x)), ((nb074_alpha_dummy_049),
        (nb074_alpha_dummy_050 x)), ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)),
        ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001),
        (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003),
        (nb074_alpha_dummy_004 x))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cv (TAlphaVar.there (show
        (nb074_alpha_dummy_053) ≠ (nb074_alpha_dummy_057) from (by
          unfold nb074_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0052) 0)))) (show (nb074_alpha_dummy_055 x) ≠
        (nb074_alpha_dummy_058 x) from (by
          unfold nb074_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb074_alpha_dummy_053) ≠ (nb074_alpha_dummy_057) from (by
          unfold nb074_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0052) 0)))) (show (nb074_alpha_dummy_055 x) ≠
        (nb074_alpha_dummy_058 x) from (by
          unfold nb074_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed [((nb074_alpha_dummy_057),
        (nb074_alpha_dummy_058 x)), ((nb074_alpha_dummy_053), (nb074_alpha_dummy_055 x)),
        ((nb074_alpha_dummy_054), (nb074_alpha_dummy_056 x)), ((nb074_alpha_dummy_046),
        (nb074_alpha_dummy_048 x)), ((nb074_alpha_dummy_045), (nb074_alpha_dummy_047 x)),
        ((nb074_alpha_dummy_051), (nb074_alpha_dummy_052 x)), ((nb074_alpha_dummy_049),
        (nb074_alpha_dummy_050 x)), ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)),
        ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001),
        (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003),
        (nb074_alpha_dummy_004 x))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb074_split_alpha_0003 x)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb074_split_alpha_0003 x)))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C074C001Part009`. -/


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
noncomputable def nb074_split_alpha_0005 (x : Var) :
    TAlphaWff
      [((nb074_alpha_dummy_093), (nb074_alpha_dummy_094 x)),
        ((nb074_alpha_dummy_091), (nb074_alpha_dummy_092 x)),
        ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)),
        ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)),
        ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)),
        ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)),
        ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)),
        ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)),
        ((nb074_alpha_dummy_000), x),
        ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
      (Wff.imp (Wff.classMem (Class.cv (nb074_alpha_dummy_093))
          (Class.cab (nb074_alpha_dummy_087)
            (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_081))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_087))
                (syn_cphi (Class.cv (nb074_alpha_dummy_088))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb074_alpha_dummy_093)) (Class.cab (nb074_alpha_dummy_087)
              (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_081))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_087))
                  (syn_cphi (Class.cv (nb074_alpha_dummy_088)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb074_alpha_dummy_094 x))
          (Class.cab (nb074_alpha_dummy_089 x)
            (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_083 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x))
                (syn_cphi (Class.cv (nb074_alpha_dummy_090 x))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb074_alpha_dummy_094 x))
            (Class.cab (nb074_alpha_dummy_089 x)
              (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_083 x))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x))
                  (syn_cphi (Class.cv (nb074_alpha_dummy_090 x))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb074_alpha_dummy_081) ≠ (nb074_alpha_dummy_088) from
                    (by
                      unfold nb074_alpha_dummy_088;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0086) 1))))
                  (show (nb074_alpha_dummy_083 x) ≠ (nb074_alpha_dummy_090 x) from (by
                      unfold nb074_alpha_dummy_090;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0088 x) 1))))
                  (TAlphaVar.there (show (nb074_alpha_dummy_081) ≠ (nb074_alpha_dummy_087) from
                      (by
                        unfold nb074_alpha_dummy_087;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0086) 0))))
                    (show (nb074_alpha_dummy_083 x) ≠ (nb074_alpha_dummy_089 x) from (by
                        unfold nb074_alpha_dummy_089;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb074_support_mem_0088 x) 0)))) (TAlphaVar.there
                      (show (nb074_alpha_dummy_081) ≠ (nb074_alpha_dummy_093) from (by
                          unfold nb074_alpha_dummy_093;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb074_support_mem_0090) 0))))
                      (show (nb074_alpha_dummy_083 x) ≠ (nb074_alpha_dummy_094 x) from (by
                          unfold nb074_alpha_dummy_094;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb074_support_mem_0091 x) 0))))
                      (TAlphaVar.there
                        (show (nb074_alpha_dummy_081) ≠ (nb074_alpha_dummy_091) from (by
                            unfold nb074_alpha_dummy_091;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb074_support_mem_0087) 0))))
                        (show (nb074_alpha_dummy_083 x) ≠ (nb074_alpha_dummy_092 x) from (by
                            unfold nb074_alpha_dummy_092;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb074_support_mem_0089 x) 0))))
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb074_alpha_dummy_000))).fv)
                            (by decide)) (freshVar_injective (((Class.cv x)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_081))).fv ∪
                      ((Class.cv (nb074_alpha_dummy_082))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb074_alpha_dummy_083 x))).fv ∪
                      ((Class.cv (nb074_alpha_dummy_084 x))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb074_alpha_dummy_088) ≠ (nb074_alpha_dummy_095) from (by
                              unfold nb074_alpha_dummy_095;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb074_support_mem_0092) 0))))
                          (show (nb074_alpha_dummy_090 x) ≠ (nb074_alpha_dummy_097 x) from (by
                              unfold nb074_alpha_dummy_097;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb074_support_mem_0093 x) 0))))
                          (TAlphaVar.there
                            (show (nb074_alpha_dummy_088) ≠ (nb074_alpha_dummy_096) from (by
                                unfold nb074_alpha_dummy_096;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb074_support_mem_0092) 1))))
                            (show (nb074_alpha_dummy_090 x) ≠ (nb074_alpha_dummy_098 x) from (by
                                unfold nb074_alpha_dummy_098;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb074_support_mem_0093 x) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb074_alpha_dummy_088))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb074_alpha_dummy_090 x))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_095) ≠ (nb074_alpha_dummy_102) from (by
          unfold nb074_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0096) 1)))) (show (nb074_alpha_dummy_097 x) ≠
        (nb074_alpha_dummy_105 x) from (by
          unfold nb074_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0097 x) 1)))) (TAlphaVar.there (show
        (nb074_alpha_dummy_095) ≠ (nb074_alpha_dummy_101) from (by
          unfold nb074_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0096) 0)))) (show (nb074_alpha_dummy_097 x) ≠
        (nb074_alpha_dummy_104 x) from (by
          unfold nb074_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0097 x) 0)))) (TAlphaVar.there (show
        (nb074_alpha_dummy_095) ≠ (nb074_alpha_dummy_099) from (by
          unfold nb074_alpha_dummy_099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0094) 0)))) (show (nb074_alpha_dummy_097 x) ≠
        (nb074_alpha_dummy_100 x) from (by
          unfold nb074_alpha_dummy_100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0095 x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb074_alpha_dummy_103), (nb074_alpha_dummy_106 x)), ((nb074_alpha_dummy_102),
        (nb074_alpha_dummy_105 x)), ((nb074_alpha_dummy_101), (nb074_alpha_dummy_104 x)),
        ((nb074_alpha_dummy_099), (nb074_alpha_dummy_100 x)), ((nb074_alpha_dummy_095),
        (nb074_alpha_dummy_097 x)), ((nb074_alpha_dummy_096), (nb074_alpha_dummy_098 x)),
        ((nb074_alpha_dummy_088), (nb074_alpha_dummy_090 x)), ((nb074_alpha_dummy_087),
        (nb074_alpha_dummy_089 x)), ((nb074_alpha_dummy_093), (nb074_alpha_dummy_094 x)),
        ((nb074_alpha_dummy_091), (nb074_alpha_dummy_092 x)), ((nb074_alpha_dummy_082),
        (nb074_alpha_dummy_084 x)), ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)),
        ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)), ((nb074_alpha_dummy_042),
        (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)),
        ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x),
        ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_102) ≠ (nb074_alpha_dummy_109) from (by
          unfold
            nb074_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0100)
                  0)))) (show (nb074_alpha_dummy_105 x) ≠ (nb074_alpha_dummy_110 x) from (by
          unfold
            nb074_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0101
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_102) ≠ (nb074_alpha_dummy_107)
        from (by
          unfold
            nb074_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0098)
                  0)))) (show (nb074_alpha_dummy_105 x) ≠ (nb074_alpha_dummy_108 x) from (by
          unfold
            nb074_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0099
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_103) ≠ (nb074_alpha_dummy_109)
        from (by
          unfold
            nb074_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0104)
                  0)))) (show (nb074_alpha_dummy_106 x) ≠ (nb074_alpha_dummy_110 x) from (by
          unfold
            nb074_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0105
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_103) ≠ (nb074_alpha_dummy_107)
        from (by
          unfold
            nb074_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0102)
                  0)))) (show (nb074_alpha_dummy_106 x) ≠ (nb074_alpha_dummy_108 x) from (by
          unfold
            nb074_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0103
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_102) ≠ (nb074_alpha_dummy_109) from (by
          unfold
            nb074_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0100)
                  0)))) (show (nb074_alpha_dummy_105 x) ≠ (nb074_alpha_dummy_110 x) from (by
          unfold
            nb074_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0101
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_102) ≠ (nb074_alpha_dummy_107)
        from (by
          unfold
            nb074_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0098)
                  0)))) (show (nb074_alpha_dummy_105 x) ≠ (nb074_alpha_dummy_108 x) from (by
          unfold
            nb074_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0099
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_103) ≠ (nb074_alpha_dummy_109)
        from (by
          unfold
            nb074_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0104)
                  0)))) (show (nb074_alpha_dummy_106 x) ≠ (nb074_alpha_dummy_110 x) from (by
          unfold
            nb074_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0105
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_103) ≠ (nb074_alpha_dummy_107)
        from (by
          unfold
            nb074_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0102)
                  0)))) (show (nb074_alpha_dummy_106 x) ≠ (nb074_alpha_dummy_108 x) from (by
          unfold
            nb074_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0103
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb074_alpha_dummy_103), (nb074_alpha_dummy_106 x)), ((nb074_alpha_dummy_102),
        (nb074_alpha_dummy_105 x)), ((nb074_alpha_dummy_101), (nb074_alpha_dummy_104 x)),
        ((nb074_alpha_dummy_099), (nb074_alpha_dummy_100 x)), ((nb074_alpha_dummy_095),
        (nb074_alpha_dummy_097 x)), ((nb074_alpha_dummy_096), (nb074_alpha_dummy_098 x)),
        ((nb074_alpha_dummy_088), (nb074_alpha_dummy_090 x)), ((nb074_alpha_dummy_087),
        (nb074_alpha_dummy_089 x)), ((nb074_alpha_dummy_093), (nb074_alpha_dummy_094 x)),
        ((nb074_alpha_dummy_091), (nb074_alpha_dummy_092 x)), ((nb074_alpha_dummy_082),
        (nb074_alpha_dummy_084 x)), ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)),
        ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)), ((nb074_alpha_dummy_042),
        (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)),
        ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x),
        ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_095))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_102) ≠
        (nb074_alpha_dummy_113) from (by
          unfold
            nb074_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0108)
                  0)))) (show (nb074_alpha_dummy_105 x) ≠ (nb074_alpha_dummy_114 x) from (by
          unfold
            nb074_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0109
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_102) ≠ (nb074_alpha_dummy_111)
        from (by
          unfold
            nb074_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0106)
                  0)))) (show (nb074_alpha_dummy_105 x) ≠ (nb074_alpha_dummy_112 x) from (by
          unfold
            nb074_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0107
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_102) ≠ (nb074_alpha_dummy_113)
        from (by
          unfold
            nb074_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0108)
                  0)))) (show (nb074_alpha_dummy_105 x) ≠ (nb074_alpha_dummy_114 x) from (by
          unfold
            nb074_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0109
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_102) ≠ (nb074_alpha_dummy_111)
        from (by
          unfold
            nb074_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0106)
                  0)))) (show (nb074_alpha_dummy_105 x) ≠ (nb074_alpha_dummy_112 x) from (by
          unfold
            nb074_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0107
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_103) ≠ (nb074_alpha_dummy_115) from (by
          unfold
            nb074_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0112)
                  0)))) (show (nb074_alpha_dummy_106 x) ≠ (nb074_alpha_dummy_116 x) from (by
          unfold
            nb074_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0113
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_103) ≠ (nb074_alpha_dummy_111)
        from (by
          unfold
            nb074_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0110)
                  0)))) (show (nb074_alpha_dummy_106 x) ≠ (nb074_alpha_dummy_112 x) from (by
          unfold
            nb074_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0111
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_103) ≠
        (nb074_alpha_dummy_115) from (by
          unfold
            nb074_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0112)
                  0)))) (show (nb074_alpha_dummy_106 x) ≠ (nb074_alpha_dummy_116 x) from (by
          unfold
            nb074_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0113
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_103) ≠ (nb074_alpha_dummy_111)
        from (by
          unfold
            nb074_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0110)
                  0)))) (show (nb074_alpha_dummy_106 x) ≠ (nb074_alpha_dummy_112 x) from (by
          unfold
            nb074_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0111
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb074_alpha_dummy_095) ≠ (nb074_alpha_dummy_099) from (by
                                        unfold nb074_alpha_dummy_099;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0094)
                                                0)))) (show (nb074_alpha_dummy_097 x) ≠
                                        (nb074_alpha_dummy_100 x) from (by
                                        unfold nb074_alpha_dummy_100;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0095 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb074_alpha_dummy_099), (nb074_alpha_dummy_100 x)),
                                    ((nb074_alpha_dummy_095), (nb074_alpha_dummy_097 x)),
                                    ((nb074_alpha_dummy_096), (nb074_alpha_dummy_098 x)),
                                    ((nb074_alpha_dummy_088), (nb074_alpha_dummy_090 x)),
                                    ((nb074_alpha_dummy_087), (nb074_alpha_dummy_089 x)),
                                    ((nb074_alpha_dummy_093), (nb074_alpha_dummy_094 x)),
                                    ((nb074_alpha_dummy_091), (nb074_alpha_dummy_092 x)),
                                    ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)),
                                    ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)),
                                    ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)),
                                    ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)),
                                    ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)),
                                    ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)),
                                    ((nb074_alpha_dummy_000), x),
                                    ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb074_alpha_dummy_095) ≠ (nb074_alpha_dummy_099) from
                                    (by
                                      unfold nb074_alpha_dummy_099;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb074_support_mem_0094)
                                              0)))) (show
                                    (nb074_alpha_dummy_097 x) ≠ (nb074_alpha_dummy_100 x) from
                                    (by
                                      unfold nb074_alpha_dummy_100;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb074_support_mem_0095 x)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb074_alpha_dummy_095) ≠ (nb074_alpha_dummy_099) from (by
                                        unfold nb074_alpha_dummy_099;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0094)
                                                0)))) (show (nb074_alpha_dummy_097 x) ≠
                                        (nb074_alpha_dummy_100 x) from (by
                                        unfold nb074_alpha_dummy_100;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0095 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb074_alpha_dummy_099), (nb074_alpha_dummy_100 x)),
                                    ((nb074_alpha_dummy_095), (nb074_alpha_dummy_097 x)),
                                    ((nb074_alpha_dummy_096), (nb074_alpha_dummy_098 x)),
                                    ((nb074_alpha_dummy_088), (nb074_alpha_dummy_090 x)),
                                    ((nb074_alpha_dummy_087), (nb074_alpha_dummy_089 x)),
                                    ((nb074_alpha_dummy_093), (nb074_alpha_dummy_094 x)),
                                    ((nb074_alpha_dummy_091), (nb074_alpha_dummy_092 x)),
                                    ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)),
                                    ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)),
                                    ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)),
                                    ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)),
                                    ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)),
                                    ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)),
                                    ((nb074_alpha_dummy_000), x),
                                    ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb074_alpha_dummy_081) ≠ (nb074_alpha_dummy_088) from
                      (by
                        unfold nb074_alpha_dummy_088;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0086) 1))))
                    (show (nb074_alpha_dummy_083 x) ≠ (nb074_alpha_dummy_090 x) from (by
                        unfold nb074_alpha_dummy_090;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb074_support_mem_0088 x) 1)))) (TAlphaVar.there
                      (show (nb074_alpha_dummy_081) ≠ (nb074_alpha_dummy_087) from (by
                          unfold nb074_alpha_dummy_087;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb074_support_mem_0086) 0))))
                      (show (nb074_alpha_dummy_083 x) ≠ (nb074_alpha_dummy_089 x) from (by
                          unfold nb074_alpha_dummy_089;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb074_support_mem_0088 x) 0))))
                      (TAlphaVar.there
                        (show (nb074_alpha_dummy_081) ≠ (nb074_alpha_dummy_093) from (by
                            unfold nb074_alpha_dummy_093;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb074_support_mem_0090) 0))))
                        (show (nb074_alpha_dummy_083 x) ≠ (nb074_alpha_dummy_094 x) from (by
                            unfold nb074_alpha_dummy_094;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb074_support_mem_0091 x) 0))))
                        (TAlphaVar.there
                          (show (nb074_alpha_dummy_081) ≠ (nb074_alpha_dummy_091) from (by
                              unfold nb074_alpha_dummy_091;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb074_support_mem_0087) 0))))
                          (show (nb074_alpha_dummy_083 x) ≠ (nb074_alpha_dummy_092 x) from (by
                              unfold nb074_alpha_dummy_092;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb074_support_mem_0089 x) 0))))
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb074_alpha_dummy_000))).fv)
                              (by decide)) (freshVar_injective (((Class.cv x)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb074_alpha_dummy_081))).fv ∪
                        ((Class.cv (nb074_alpha_dummy_082))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb074_alpha_dummy_083 x))).fv ∪
                        ((Class.cv (nb074_alpha_dummy_084 x))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb074_alpha_dummy_088) ≠ (nb074_alpha_dummy_095) from (by
                                unfold nb074_alpha_dummy_095;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb074_support_mem_0092) 0))))
                            (show (nb074_alpha_dummy_090 x) ≠ (nb074_alpha_dummy_097 x) from (by
                                unfold nb074_alpha_dummy_097;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb074_support_mem_0093 x) 0))))
                            (TAlphaVar.there
                              (show (nb074_alpha_dummy_088) ≠ (nb074_alpha_dummy_096) from (by
                                  unfold nb074_alpha_dummy_096;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb074_support_mem_0092) 1))))
                              (show (nb074_alpha_dummy_090 x) ≠ (nb074_alpha_dummy_098 x) from
                                (by
                                  unfold nb074_alpha_dummy_098;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb074_support_mem_0093 x) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb074_alpha_dummy_088))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb074_alpha_dummy_090 x))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb074_alpha_dummy_095) ≠ (nb074_alpha_dummy_102) from (by
          unfold nb074_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0096) 1)))) (show (nb074_alpha_dummy_097 x) ≠
        (nb074_alpha_dummy_105 x) from (by
          unfold nb074_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0097 x) 1)))) (TAlphaVar.there (show
        (nb074_alpha_dummy_095) ≠ (nb074_alpha_dummy_101) from (by
          unfold nb074_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0096) 0)))) (show (nb074_alpha_dummy_097 x) ≠
        (nb074_alpha_dummy_104 x) from (by
          unfold nb074_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0097 x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_095) ≠ (nb074_alpha_dummy_099)
        from (by
          unfold nb074_alpha_dummy_099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0094)
                  0)))) (show (nb074_alpha_dummy_097 x) ≠ (nb074_alpha_dummy_100 x) from (by
          unfold nb074_alpha_dummy_100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0095 x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb074_alpha_dummy_103), (nb074_alpha_dummy_106 x)), ((nb074_alpha_dummy_102),
        (nb074_alpha_dummy_105 x)), ((nb074_alpha_dummy_101), (nb074_alpha_dummy_104 x)),
        ((nb074_alpha_dummy_099), (nb074_alpha_dummy_100 x)), ((nb074_alpha_dummy_095),
        (nb074_alpha_dummy_097 x)), ((nb074_alpha_dummy_096), (nb074_alpha_dummy_098 x)),
        ((nb074_alpha_dummy_088), (nb074_alpha_dummy_090 x)), ((nb074_alpha_dummy_087),
        (nb074_alpha_dummy_089 x)), ((nb074_alpha_dummy_093), (nb074_alpha_dummy_094 x)),
        ((nb074_alpha_dummy_091), (nb074_alpha_dummy_092 x)), ((nb074_alpha_dummy_082),
        (nb074_alpha_dummy_084 x)), ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)),
        ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)), ((nb074_alpha_dummy_042),
        (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)),
        ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x),
        ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_102) ≠ (nb074_alpha_dummy_109) from (by
          unfold
            nb074_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0100)
                  0)))) (show (nb074_alpha_dummy_105 x) ≠ (nb074_alpha_dummy_110 x) from (by
          unfold
            nb074_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0101
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_102) ≠ (nb074_alpha_dummy_107)
        from (by
          unfold
            nb074_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0098)
                  0)))) (show (nb074_alpha_dummy_105 x) ≠ (nb074_alpha_dummy_108 x) from (by
          unfold
            nb074_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0099
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_103) ≠ (nb074_alpha_dummy_109)
        from (by
          unfold
            nb074_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0104)
                  0)))) (show (nb074_alpha_dummy_106 x) ≠ (nb074_alpha_dummy_110 x) from (by
          unfold
            nb074_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0105
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_103) ≠ (nb074_alpha_dummy_107)
        from (by
          unfold
            nb074_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0102)
                  0)))) (show (nb074_alpha_dummy_106 x) ≠ (nb074_alpha_dummy_108 x) from (by
          unfold
            nb074_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0103
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_102) ≠ (nb074_alpha_dummy_109) from (by
          unfold
            nb074_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0100)
                  0)))) (show (nb074_alpha_dummy_105 x) ≠ (nb074_alpha_dummy_110 x) from (by
          unfold
            nb074_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0101
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_102) ≠ (nb074_alpha_dummy_107)
        from (by
          unfold
            nb074_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0098)
                  0)))) (show (nb074_alpha_dummy_105 x) ≠ (nb074_alpha_dummy_108 x) from (by
          unfold
            nb074_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0099
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_103) ≠ (nb074_alpha_dummy_109)
        from (by
          unfold
            nb074_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0104)
                  0)))) (show (nb074_alpha_dummy_106 x) ≠ (nb074_alpha_dummy_110 x) from (by
          unfold
            nb074_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0105
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_103) ≠ (nb074_alpha_dummy_107)
        from (by
          unfold
            nb074_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0102)
                  0)))) (show (nb074_alpha_dummy_106 x) ≠ (nb074_alpha_dummy_108 x) from (by
          unfold
            nb074_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0103
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb074_alpha_dummy_103), (nb074_alpha_dummy_106 x)), ((nb074_alpha_dummy_102),
        (nb074_alpha_dummy_105 x)), ((nb074_alpha_dummy_101), (nb074_alpha_dummy_104 x)),
        ((nb074_alpha_dummy_099), (nb074_alpha_dummy_100 x)), ((nb074_alpha_dummy_095),
        (nb074_alpha_dummy_097 x)), ((nb074_alpha_dummy_096), (nb074_alpha_dummy_098 x)),
        ((nb074_alpha_dummy_088), (nb074_alpha_dummy_090 x)), ((nb074_alpha_dummy_087),
        (nb074_alpha_dummy_089 x)), ((nb074_alpha_dummy_093), (nb074_alpha_dummy_094 x)),
        ((nb074_alpha_dummy_091), (nb074_alpha_dummy_092 x)), ((nb074_alpha_dummy_082),
        (nb074_alpha_dummy_084 x)), ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)),
        ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)), ((nb074_alpha_dummy_042),
        (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)),
        ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x),
        ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_095))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_097
        x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_102) ≠
        (nb074_alpha_dummy_113) from (by
          unfold
            nb074_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0108)
                  0)))) (show (nb074_alpha_dummy_105 x) ≠ (nb074_alpha_dummy_114 x) from (by
          unfold
            nb074_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0109
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_102) ≠ (nb074_alpha_dummy_111)
        from (by
          unfold
            nb074_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0106)
                  0)))) (show (nb074_alpha_dummy_105 x) ≠ (nb074_alpha_dummy_112 x) from (by
          unfold
            nb074_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0107
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_102) ≠ (nb074_alpha_dummy_113)
        from (by
          unfold
            nb074_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0108)
                  0)))) (show (nb074_alpha_dummy_105 x) ≠ (nb074_alpha_dummy_114 x) from (by
          unfold
            nb074_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0109
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_102) ≠ (nb074_alpha_dummy_111)
        from (by
          unfold
            nb074_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0106)
                  0)))) (show (nb074_alpha_dummy_105 x) ≠ (nb074_alpha_dummy_112 x) from (by
          unfold
            nb074_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0107
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_103) ≠ (nb074_alpha_dummy_115) from (by
          unfold
            nb074_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0112)
                  0)))) (show (nb074_alpha_dummy_106 x) ≠ (nb074_alpha_dummy_116 x) from (by
          unfold
            nb074_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0113
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_103) ≠ (nb074_alpha_dummy_111)
        from (by
          unfold
            nb074_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0110)
                  0)))) (show (nb074_alpha_dummy_106 x) ≠ (nb074_alpha_dummy_112 x) from (by
          unfold
            nb074_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0111
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_103) ≠
        (nb074_alpha_dummy_115) from (by
          unfold
            nb074_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0112)
                  0)))) (show (nb074_alpha_dummy_106 x) ≠ (nb074_alpha_dummy_116 x) from (by
          unfold
            nb074_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0113
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_103) ≠ (nb074_alpha_dummy_111)
        from (by
          unfold
            nb074_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0110)
                  0)))) (show (nb074_alpha_dummy_106 x) ≠ (nb074_alpha_dummy_112 x) from (by
          unfold
            nb074_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0111
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb074_alpha_dummy_095) ≠ (nb074_alpha_dummy_099) from
                                        (by
                                          unfold nb074_alpha_dummy_099;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb074_support_mem_0094)
                                                  0)))) (show (nb074_alpha_dummy_097 x) ≠
        (nb074_alpha_dummy_100 x) from (by
                                          unfold nb074_alpha_dummy_100;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb074_support_mem_0095 x) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb074_alpha_dummy_099), (nb074_alpha_dummy_100 x)),
                                      ((nb074_alpha_dummy_095), (nb074_alpha_dummy_097 x)),
                                      ((nb074_alpha_dummy_096), (nb074_alpha_dummy_098 x)),
                                      ((nb074_alpha_dummy_088), (nb074_alpha_dummy_090 x)),
                                      ((nb074_alpha_dummy_087), (nb074_alpha_dummy_089 x)),
                                      ((nb074_alpha_dummy_093), (nb074_alpha_dummy_094 x)),
                                      ((nb074_alpha_dummy_091), (nb074_alpha_dummy_092 x)),
                                      ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)),
                                      ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)),
                                      ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)),
                                      ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)),
                                      ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)),
                                      ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)),
                                      ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003),
                                        (nb074_alpha_dummy_004 x))]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb074_alpha_dummy_095) ≠ (nb074_alpha_dummy_099) from (by
                                        unfold nb074_alpha_dummy_099;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0094)
                                                0)))) (show (nb074_alpha_dummy_097 x) ≠
                                        (nb074_alpha_dummy_100 x) from (by
                                        unfold nb074_alpha_dummy_100;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0095 x)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb074_alpha_dummy_095) ≠ (nb074_alpha_dummy_099) from
                                        (by
                                          unfold nb074_alpha_dummy_099;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb074_support_mem_0094)
                                                  0)))) (show (nb074_alpha_dummy_097 x) ≠
        (nb074_alpha_dummy_100 x) from (by
                                          unfold nb074_alpha_dummy_100;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb074_support_mem_0095 x) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb074_alpha_dummy_099), (nb074_alpha_dummy_100 x)),
                                      ((nb074_alpha_dummy_095), (nb074_alpha_dummy_097 x)),
                                      ((nb074_alpha_dummy_096), (nb074_alpha_dummy_098 x)),
                                      ((nb074_alpha_dummy_088), (nb074_alpha_dummy_090 x)),
                                      ((nb074_alpha_dummy_087), (nb074_alpha_dummy_089 x)),
                                      ((nb074_alpha_dummy_093), (nb074_alpha_dummy_094 x)),
                                      ((nb074_alpha_dummy_091), (nb074_alpha_dummy_092 x)),
                                      ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)),
                                      ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)),
                                      ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)),
                                      ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)),
                                      ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)),
                                      ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)),
                                      ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003),
                                        (nb074_alpha_dummy_004 x))] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
