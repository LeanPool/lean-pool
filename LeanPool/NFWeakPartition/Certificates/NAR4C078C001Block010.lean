/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block009

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part032`. -/


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
noncomputable def nb078_split_alpha_0000 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_023), (nb078_alpha_dummy_024 f)),
        ((nb078_alpha_dummy_021), (nb078_alpha_dummy_022 f)),
        ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
        ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
        ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
        ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
        ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_023))
          (Class.cab (nb078_alpha_dummy_017)
            (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_009))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_017))
                (syn_cphi (Class.cv (nb078_alpha_dummy_018))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_023)) (Class.cab (nb078_alpha_dummy_017)
              (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_009))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_017))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_018)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_024 f))
          (Class.cab (nb078_alpha_dummy_019 f)
            (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_012 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_020 f))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_024 f))
            (Class.cab (nb078_alpha_dummy_019 f)
              (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_012 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_020 f))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_009) ≠ (nb078_alpha_dummy_018) from
                    (by
                      unfold nb078_alpha_dummy_018;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0004) 1))))
                  (show (nb078_alpha_dummy_012 f) ≠ (nb078_alpha_dummy_020 f) from (by
                      unfold nb078_alpha_dummy_020;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0006 f) 1))))
                  (TAlphaVar.there (show (nb078_alpha_dummy_009) ≠ (nb078_alpha_dummy_017) from
                      (by
                        unfold nb078_alpha_dummy_017;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0004) 0))))
                    (show (nb078_alpha_dummy_012 f) ≠ (nb078_alpha_dummy_019 f) from (by
                        unfold nb078_alpha_dummy_019;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0006 f) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_009) ≠ (nb078_alpha_dummy_023) from (by
                          unfold nb078_alpha_dummy_023;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0008) 0))))
                      (show (nb078_alpha_dummy_012 f) ≠ (nb078_alpha_dummy_024 f) from (by
                          unfold nb078_alpha_dummy_024;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0009 f) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_009) ≠ (nb078_alpha_dummy_021) from (by
                            unfold nb078_alpha_dummy_021;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0005) 0))))
                        (show (nb078_alpha_dummy_012 f) ≠ (nb078_alpha_dummy_022 f) from (by
                            unfold nb078_alpha_dummy_022;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0007 f) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb078_alpha_dummy_000))).fv ∪
                              ((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv) (by decide))
                          (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb078_alpha_dummy_009))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_010))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_013 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_018) ≠ (nb078_alpha_dummy_025) from (by
                              unfold nb078_alpha_dummy_025;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0010) 0))))
                          (show (nb078_alpha_dummy_020 f) ≠ (nb078_alpha_dummy_027 f) from (by
                              unfold nb078_alpha_dummy_027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0011 f) 0))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_018) ≠ (nb078_alpha_dummy_026) from (by
                                unfold nb078_alpha_dummy_026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0010) 1))))
                            (show (nb078_alpha_dummy_020 f) ≠ (nb078_alpha_dummy_028 f) from (by
                                unfold nb078_alpha_dummy_028;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0011 f) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_018))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_020 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_025) ≠ (nb078_alpha_dummy_032) from (by
          unfold nb078_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0014) 1)))) (show (nb078_alpha_dummy_027 f) ≠
        (nb078_alpha_dummy_035 f) from (by
          unfold nb078_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0015 f) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_025) ≠ (nb078_alpha_dummy_031) from (by
          unfold nb078_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0014) 0)))) (show (nb078_alpha_dummy_027 f) ≠
        (nb078_alpha_dummy_034 f) from (by
          unfold nb078_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0015 f) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_025) ≠ (nb078_alpha_dummy_029) from (by
          unfold nb078_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0012) 0)))) (show (nb078_alpha_dummy_027 f) ≠
        (nb078_alpha_dummy_030 f) from (by
          unfold nb078_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0013 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_033), (nb078_alpha_dummy_036 f)), ((nb078_alpha_dummy_032),
        (nb078_alpha_dummy_035 f)), ((nb078_alpha_dummy_031), (nb078_alpha_dummy_034 f)),
        ((nb078_alpha_dummy_029), (nb078_alpha_dummy_030 f)), ((nb078_alpha_dummy_025),
        (nb078_alpha_dummy_027 f)), ((nb078_alpha_dummy_026), (nb078_alpha_dummy_028 f)),
        ((nb078_alpha_dummy_018), (nb078_alpha_dummy_020 f)), ((nb078_alpha_dummy_017),
        (nb078_alpha_dummy_019 f)), ((nb078_alpha_dummy_023), (nb078_alpha_dummy_024 f)),
        ((nb078_alpha_dummy_021), (nb078_alpha_dummy_022 f)), ((nb078_alpha_dummy_010),
        (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
        ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007),
        (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_032) ≠ (nb078_alpha_dummy_039) from (by
          unfold
            nb078_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0018)
                  0)))) (show (nb078_alpha_dummy_035 f) ≠ (nb078_alpha_dummy_040 f) from (by
          unfold
            nb078_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0019
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_032) ≠ (nb078_alpha_dummy_037)
        from (by
          unfold
            nb078_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0016)
                  0)))) (show (nb078_alpha_dummy_035 f) ≠ (nb078_alpha_dummy_038 f) from (by
          unfold
            nb078_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0017
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_033) ≠ (nb078_alpha_dummy_039)
        from (by
          unfold
            nb078_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0022)
                  0)))) (show (nb078_alpha_dummy_036 f) ≠ (nb078_alpha_dummy_040 f) from (by
          unfold
            nb078_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0023
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_033) ≠ (nb078_alpha_dummy_037)
        from (by
          unfold
            nb078_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0020)
                  0)))) (show (nb078_alpha_dummy_036 f) ≠ (nb078_alpha_dummy_038 f) from (by
          unfold
            nb078_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0021
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_032) ≠ (nb078_alpha_dummy_039) from (by
          unfold
            nb078_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0018)
                  0)))) (show (nb078_alpha_dummy_035 f) ≠ (nb078_alpha_dummy_040 f) from (by
          unfold
            nb078_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0019
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_032) ≠ (nb078_alpha_dummy_037)
        from (by
          unfold
            nb078_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0016)
                  0)))) (show (nb078_alpha_dummy_035 f) ≠ (nb078_alpha_dummy_038 f) from (by
          unfold
            nb078_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0017
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_033) ≠ (nb078_alpha_dummy_039)
        from (by
          unfold
            nb078_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0022)
                  0)))) (show (nb078_alpha_dummy_036 f) ≠ (nb078_alpha_dummy_040 f) from (by
          unfold
            nb078_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0023
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_033) ≠ (nb078_alpha_dummy_037)
        from (by
          unfold
            nb078_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0020)
                  0)))) (show (nb078_alpha_dummy_036 f) ≠ (nb078_alpha_dummy_038 f) from (by
          unfold
            nb078_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0021
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_033), (nb078_alpha_dummy_036 f)), ((nb078_alpha_dummy_032),
        (nb078_alpha_dummy_035 f)), ((nb078_alpha_dummy_031), (nb078_alpha_dummy_034 f)),
        ((nb078_alpha_dummy_029), (nb078_alpha_dummy_030 f)), ((nb078_alpha_dummy_025),
        (nb078_alpha_dummy_027 f)), ((nb078_alpha_dummy_026), (nb078_alpha_dummy_028 f)),
        ((nb078_alpha_dummy_018), (nb078_alpha_dummy_020 f)), ((nb078_alpha_dummy_017),
        (nb078_alpha_dummy_019 f)), ((nb078_alpha_dummy_023), (nb078_alpha_dummy_024 f)),
        ((nb078_alpha_dummy_021), (nb078_alpha_dummy_022 f)), ((nb078_alpha_dummy_010),
        (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
        ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007),
        (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_025))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_027
        f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_032) ≠ (nb078_alpha_dummy_043) from (by
          unfold
            nb078_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0026)
                  0)))) (show (nb078_alpha_dummy_035 f) ≠ (nb078_alpha_dummy_044 f) from (by
          unfold
            nb078_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0027
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_032) ≠ (nb078_alpha_dummy_041)
        from (by
          unfold
            nb078_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0024)
                  0)))) (show (nb078_alpha_dummy_035 f) ≠ (nb078_alpha_dummy_042 f) from (by
          unfold
            nb078_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0025
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_032) ≠ (nb078_alpha_dummy_043)
        from (by
          unfold
            nb078_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0026)
                  0)))) (show (nb078_alpha_dummy_035 f) ≠ (nb078_alpha_dummy_044 f) from (by
          unfold
            nb078_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0027
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_032) ≠ (nb078_alpha_dummy_041)
        from (by
          unfold
            nb078_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0024)
                  0)))) (show (nb078_alpha_dummy_035 f) ≠ (nb078_alpha_dummy_042 f) from (by
          unfold
            nb078_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0025
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_033) ≠ (nb078_alpha_dummy_045) from (by
          unfold
            nb078_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0030)
                  0)))) (show (nb078_alpha_dummy_036 f) ≠ (nb078_alpha_dummy_046 f) from (by
          unfold
            nb078_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0031
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_033) ≠ (nb078_alpha_dummy_041)
        from (by
          unfold
            nb078_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0028)
                  0)))) (show (nb078_alpha_dummy_036 f) ≠ (nb078_alpha_dummy_042 f) from (by
          unfold
            nb078_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0029
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_033) ≠
        (nb078_alpha_dummy_045) from (by
          unfold
            nb078_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0030)
                  0)))) (show (nb078_alpha_dummy_036 f) ≠ (nb078_alpha_dummy_046 f) from (by
          unfold
            nb078_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0031
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_033) ≠ (nb078_alpha_dummy_041)
        from (by
          unfold
            nb078_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0028)
                  0)))) (show (nb078_alpha_dummy_036 f) ≠ (nb078_alpha_dummy_042 f) from (by
          unfold
            nb078_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0029
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_025) ≠ (nb078_alpha_dummy_029) from (by
                                        unfold nb078_alpha_dummy_029;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0012)
                                                0)))) (show (nb078_alpha_dummy_027 f) ≠
                                        (nb078_alpha_dummy_030 f) from (by
                                        unfold nb078_alpha_dummy_030;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0013 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_029), (nb078_alpha_dummy_030 f)),
                                    ((nb078_alpha_dummy_025), (nb078_alpha_dummy_027 f)),
                                    ((nb078_alpha_dummy_026), (nb078_alpha_dummy_028 f)),
                                    ((nb078_alpha_dummy_018), (nb078_alpha_dummy_020 f)),
                                    ((nb078_alpha_dummy_017), (nb078_alpha_dummy_019 f)),
                                    ((nb078_alpha_dummy_023), (nb078_alpha_dummy_024 f)),
                                    ((nb078_alpha_dummy_021), (nb078_alpha_dummy_022 f)),
                                    ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
                                    ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
                                    ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
                                    ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
                                    ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
                                    ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_025) ≠ (nb078_alpha_dummy_029) from
                                    (by
                                      unfold nb078_alpha_dummy_029;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0012)
                                              0)))) (show
                                    (nb078_alpha_dummy_027 f) ≠ (nb078_alpha_dummy_030 f) from
                                    (by
                                      unfold nb078_alpha_dummy_030;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0013 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_025) ≠ (nb078_alpha_dummy_029) from (by
                                        unfold nb078_alpha_dummy_029;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0012)
                                                0)))) (show (nb078_alpha_dummy_027 f) ≠
                                        (nb078_alpha_dummy_030 f) from (by
                                        unfold nb078_alpha_dummy_030;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0013 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_029), (nb078_alpha_dummy_030 f)),
                                    ((nb078_alpha_dummy_025), (nb078_alpha_dummy_027 f)),
                                    ((nb078_alpha_dummy_026), (nb078_alpha_dummy_028 f)),
                                    ((nb078_alpha_dummy_018), (nb078_alpha_dummy_020 f)),
                                    ((nb078_alpha_dummy_017), (nb078_alpha_dummy_019 f)),
                                    ((nb078_alpha_dummy_023), (nb078_alpha_dummy_024 f)),
                                    ((nb078_alpha_dummy_021), (nb078_alpha_dummy_022 f)),
                                    ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
                                    ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
                                    ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
                                    ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
                                    ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
                                    ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078_alpha_dummy_009) ≠ (nb078_alpha_dummy_018) from
                      (by
                        unfold nb078_alpha_dummy_018;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0004) 1))))
                    (show (nb078_alpha_dummy_012 f) ≠ (nb078_alpha_dummy_020 f) from (by
                        unfold nb078_alpha_dummy_020;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0006 f) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_009) ≠ (nb078_alpha_dummy_017) from (by
                          unfold nb078_alpha_dummy_017;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0004) 0))))
                      (show (nb078_alpha_dummy_012 f) ≠ (nb078_alpha_dummy_019 f) from (by
                          unfold nb078_alpha_dummy_019;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0006 f) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_009) ≠ (nb078_alpha_dummy_023) from (by
                            unfold nb078_alpha_dummy_023;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0008) 0))))
                        (show (nb078_alpha_dummy_012 f) ≠ (nb078_alpha_dummy_024 f) from (by
                            unfold nb078_alpha_dummy_024;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0009 f) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_009) ≠ (nb078_alpha_dummy_021) from (by
                              unfold nb078_alpha_dummy_021;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0005) 0))))
                          (show (nb078_alpha_dummy_012 f) ≠ (nb078_alpha_dummy_022 f) from (by
                              unfold nb078_alpha_dummy_022;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0007 f) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_000))).fv ∪
                                ((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078_alpha_dummy_009))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_010))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_013 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_018) ≠ (nb078_alpha_dummy_025) from (by
                                unfold nb078_alpha_dummy_025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0010) 0))))
                            (show (nb078_alpha_dummy_020 f) ≠ (nb078_alpha_dummy_027 f) from (by
                                unfold nb078_alpha_dummy_027;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0011 f) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_018) ≠ (nb078_alpha_dummy_026) from (by
                                  unfold nb078_alpha_dummy_026;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0010) 1))))
                              (show (nb078_alpha_dummy_020 f) ≠ (nb078_alpha_dummy_028 f) from
                                (by
                                  unfold nb078_alpha_dummy_028;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0011 f) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_018))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_020 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_025) ≠ (nb078_alpha_dummy_032) from (by
          unfold nb078_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0014) 1)))) (show (nb078_alpha_dummy_027 f) ≠
        (nb078_alpha_dummy_035 f) from (by
          unfold nb078_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0015 f) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_025) ≠ (nb078_alpha_dummy_031) from (by
          unfold nb078_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0014) 0)))) (show (nb078_alpha_dummy_027 f) ≠
        (nb078_alpha_dummy_034 f) from (by
          unfold nb078_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0015 f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_025) ≠ (nb078_alpha_dummy_029)
        from (by
          unfold nb078_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0012)
                  0)))) (show (nb078_alpha_dummy_027 f) ≠ (nb078_alpha_dummy_030 f) from (by
          unfold nb078_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0013 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_033), (nb078_alpha_dummy_036 f)), ((nb078_alpha_dummy_032),
        (nb078_alpha_dummy_035 f)), ((nb078_alpha_dummy_031), (nb078_alpha_dummy_034 f)),
        ((nb078_alpha_dummy_029), (nb078_alpha_dummy_030 f)), ((nb078_alpha_dummy_025),
        (nb078_alpha_dummy_027 f)), ((nb078_alpha_dummy_026), (nb078_alpha_dummy_028 f)),
        ((nb078_alpha_dummy_018), (nb078_alpha_dummy_020 f)), ((nb078_alpha_dummy_017),
        (nb078_alpha_dummy_019 f)), ((nb078_alpha_dummy_023), (nb078_alpha_dummy_024 f)),
        ((nb078_alpha_dummy_021), (nb078_alpha_dummy_022 f)), ((nb078_alpha_dummy_010),
        (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
        ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007),
        (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_032) ≠ (nb078_alpha_dummy_039) from (by
          unfold
            nb078_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0018)
                  0)))) (show (nb078_alpha_dummy_035 f) ≠ (nb078_alpha_dummy_040 f) from (by
          unfold
            nb078_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0019
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_032) ≠ (nb078_alpha_dummy_037)
        from (by
          unfold
            nb078_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0016)
                  0)))) (show (nb078_alpha_dummy_035 f) ≠ (nb078_alpha_dummy_038 f) from (by
          unfold
            nb078_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0017
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_033) ≠ (nb078_alpha_dummy_039)
        from (by
          unfold
            nb078_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0022)
                  0)))) (show (nb078_alpha_dummy_036 f) ≠ (nb078_alpha_dummy_040 f) from (by
          unfold
            nb078_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0023
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_033) ≠ (nb078_alpha_dummy_037)
        from (by
          unfold
            nb078_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0020)
                  0)))) (show (nb078_alpha_dummy_036 f) ≠ (nb078_alpha_dummy_038 f) from (by
          unfold
            nb078_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0021
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_032) ≠ (nb078_alpha_dummy_039) from (by
          unfold
            nb078_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0018)
                  0)))) (show (nb078_alpha_dummy_035 f) ≠ (nb078_alpha_dummy_040 f) from (by
          unfold
            nb078_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0019
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_032) ≠ (nb078_alpha_dummy_037)
        from (by
          unfold
            nb078_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0016)
                  0)))) (show (nb078_alpha_dummy_035 f) ≠ (nb078_alpha_dummy_038 f) from (by
          unfold
            nb078_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0017
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_033) ≠ (nb078_alpha_dummy_039)
        from (by
          unfold
            nb078_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0022)
                  0)))) (show (nb078_alpha_dummy_036 f) ≠ (nb078_alpha_dummy_040 f) from (by
          unfold
            nb078_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0023
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_033) ≠ (nb078_alpha_dummy_037)
        from (by
          unfold
            nb078_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0020)
                  0)))) (show (nb078_alpha_dummy_036 f) ≠ (nb078_alpha_dummy_038 f) from (by
          unfold
            nb078_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0021
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_033), (nb078_alpha_dummy_036 f)), ((nb078_alpha_dummy_032),
        (nb078_alpha_dummy_035 f)), ((nb078_alpha_dummy_031), (nb078_alpha_dummy_034 f)),
        ((nb078_alpha_dummy_029), (nb078_alpha_dummy_030 f)), ((nb078_alpha_dummy_025),
        (nb078_alpha_dummy_027 f)), ((nb078_alpha_dummy_026), (nb078_alpha_dummy_028 f)),
        ((nb078_alpha_dummy_018), (nb078_alpha_dummy_020 f)), ((nb078_alpha_dummy_017),
        (nb078_alpha_dummy_019 f)), ((nb078_alpha_dummy_023), (nb078_alpha_dummy_024 f)),
        ((nb078_alpha_dummy_021), (nb078_alpha_dummy_022 f)), ((nb078_alpha_dummy_010),
        (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
        ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007),
        (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_025))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_027
        f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_032) ≠ (nb078_alpha_dummy_043) from (by
          unfold
            nb078_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0026)
                  0)))) (show (nb078_alpha_dummy_035 f) ≠ (nb078_alpha_dummy_044 f) from (by
          unfold
            nb078_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0027
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_032) ≠ (nb078_alpha_dummy_041)
        from (by
          unfold
            nb078_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0024)
                  0)))) (show (nb078_alpha_dummy_035 f) ≠ (nb078_alpha_dummy_042 f) from (by
          unfold
            nb078_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0025
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_032) ≠ (nb078_alpha_dummy_043)
        from (by
          unfold
            nb078_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0026)
                  0)))) (show (nb078_alpha_dummy_035 f) ≠ (nb078_alpha_dummy_044 f) from (by
          unfold
            nb078_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0027
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_032) ≠ (nb078_alpha_dummy_041)
        from (by
          unfold
            nb078_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0024)
                  0)))) (show (nb078_alpha_dummy_035 f) ≠ (nb078_alpha_dummy_042 f) from (by
          unfold
            nb078_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0025
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_033) ≠ (nb078_alpha_dummy_045) from (by
          unfold
            nb078_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0030)
                  0)))) (show (nb078_alpha_dummy_036 f) ≠ (nb078_alpha_dummy_046 f) from (by
          unfold
            nb078_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0031
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_033) ≠ (nb078_alpha_dummy_041)
        from (by
          unfold
            nb078_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0028)
                  0)))) (show (nb078_alpha_dummy_036 f) ≠ (nb078_alpha_dummy_042 f) from (by
          unfold
            nb078_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0029
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_033) ≠
        (nb078_alpha_dummy_045) from (by
          unfold
            nb078_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0030)
                  0)))) (show (nb078_alpha_dummy_036 f) ≠ (nb078_alpha_dummy_046 f) from (by
          unfold
            nb078_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0031
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_033) ≠ (nb078_alpha_dummy_041)
        from (by
          unfold
            nb078_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0028)
                  0)))) (show (nb078_alpha_dummy_036 f) ≠ (nb078_alpha_dummy_042 f) from (by
          unfold
            nb078_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0029
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_025) ≠ (nb078_alpha_dummy_029) from
                                        (by
                                          unfold nb078_alpha_dummy_029;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0012)
                                                  0)))) (show (nb078_alpha_dummy_027 f) ≠
        (nb078_alpha_dummy_030 f) from (by
                                          unfold nb078_alpha_dummy_030;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0013 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_029), (nb078_alpha_dummy_030 f)),
                                      ((nb078_alpha_dummy_025), (nb078_alpha_dummy_027 f)),
                                      ((nb078_alpha_dummy_026), (nb078_alpha_dummy_028 f)),
                                      ((nb078_alpha_dummy_018), (nb078_alpha_dummy_020 f)),
                                      ((nb078_alpha_dummy_017), (nb078_alpha_dummy_019 f)),
                                      ((nb078_alpha_dummy_023), (nb078_alpha_dummy_024 f)),
                                      ((nb078_alpha_dummy_021), (nb078_alpha_dummy_022 f)),
                                      ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
                                      ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
                                      ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
                                      ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
                                      ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
                                      ((nb078_alpha_dummy_000), f),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_025) ≠ (nb078_alpha_dummy_029) from (by
                                        unfold nb078_alpha_dummy_029;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0012)
                                                0)))) (show (nb078_alpha_dummy_027 f) ≠
                                        (nb078_alpha_dummy_030 f) from (by
                                        unfold nb078_alpha_dummy_030;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0013 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_025) ≠ (nb078_alpha_dummy_029) from
                                        (by
                                          unfold nb078_alpha_dummy_029;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0012)
                                                  0)))) (show (nb078_alpha_dummy_027 f) ≠
        (nb078_alpha_dummy_030 f) from (by
                                          unfold nb078_alpha_dummy_030;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0013 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_029), (nb078_alpha_dummy_030 f)),
                                      ((nb078_alpha_dummy_025), (nb078_alpha_dummy_027 f)),
                                      ((nb078_alpha_dummy_026), (nb078_alpha_dummy_028 f)),
                                      ((nb078_alpha_dummy_018), (nb078_alpha_dummy_020 f)),
                                      ((nb078_alpha_dummy_017), (nb078_alpha_dummy_019 f)),
                                      ((nb078_alpha_dummy_023), (nb078_alpha_dummy_024 f)),
                                      ((nb078_alpha_dummy_021), (nb078_alpha_dummy_022 f)),
                                      ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
                                      ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
                                      ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
                                      ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
                                      ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
                                      ((nb078_alpha_dummy_000), f),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part033`. -/


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
noncomputable def nb078_split_alpha_0001 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_049), (nb078_alpha_dummy_050 f)),
        ((nb078_alpha_dummy_018), (nb078_alpha_dummy_020 f)),
        ((nb078_alpha_dummy_017), (nb078_alpha_dummy_019 f)),
        ((nb078_alpha_dummy_047), (nb078_alpha_dummy_048 f)),
        ((nb078_alpha_dummy_021), (nb078_alpha_dummy_022 f)),
        ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
        ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
        ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
        ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
        ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_049))
          (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_018))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_049)) (syn_ccompl (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_050 f))
          (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_020 f))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_050 f))
            (syn_ccompl (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_018) ≠ (nb078_alpha_dummy_025) from (by
                              unfold nb078_alpha_dummy_025;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0010) 0))))
                          (show (nb078_alpha_dummy_020 f) ≠ (nb078_alpha_dummy_027 f) from (by
                              unfold nb078_alpha_dummy_027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0011 f) 0))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_018) ≠ (nb078_alpha_dummy_026) from (by
                                unfold nb078_alpha_dummy_026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0010) 1))))
                            (show (nb078_alpha_dummy_020 f) ≠ (nb078_alpha_dummy_028 f) from (by
                                unfold nb078_alpha_dummy_028;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0011 f) 1))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_018) ≠ (nb078_alpha_dummy_051) from (by
                                  unfold nb078_alpha_dummy_051;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0040) 0))))
                              (show (nb078_alpha_dummy_020 f) ≠ (nb078_alpha_dummy_052 f) from
                                (by
                                  unfold nb078_alpha_dummy_052;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0041 f) 0))))
                              (TAlphaVar.there
                                (show (nb078_alpha_dummy_018) ≠ (nb078_alpha_dummy_049) from (by
                                    unfold nb078_alpha_dummy_049;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0038) 0)))) (show
                                  (nb078_alpha_dummy_020 f) ≠ (nb078_alpha_dummy_050 f) from (by
                                    unfold nb078_alpha_dummy_050;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0039 f)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_018))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_020 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_025) ≠ (nb078_alpha_dummy_032) from (by
          unfold nb078_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0014) 1)))) (show (nb078_alpha_dummy_027 f) ≠
        (nb078_alpha_dummy_035 f) from (by
          unfold nb078_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0015 f) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_025) ≠ (nb078_alpha_dummy_031) from (by
          unfold nb078_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0014) 0)))) (show (nb078_alpha_dummy_027 f) ≠
        (nb078_alpha_dummy_034 f) from (by
          unfold nb078_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0015 f) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_025) ≠ (nb078_alpha_dummy_029) from (by
          unfold nb078_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0012) 0)))) (show (nb078_alpha_dummy_027 f) ≠
        (nb078_alpha_dummy_030 f) from (by
          unfold nb078_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0013 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_033), (nb078_alpha_dummy_036 f)), ((nb078_alpha_dummy_032),
        (nb078_alpha_dummy_035 f)), ((nb078_alpha_dummy_031), (nb078_alpha_dummy_034 f)),
        ((nb078_alpha_dummy_029), (nb078_alpha_dummy_030 f)), ((nb078_alpha_dummy_025),
        (nb078_alpha_dummy_027 f)), ((nb078_alpha_dummy_026), (nb078_alpha_dummy_028 f)),
        ((nb078_alpha_dummy_051), (nb078_alpha_dummy_052 f)), ((nb078_alpha_dummy_049),
        (nb078_alpha_dummy_050 f)), ((nb078_alpha_dummy_018), (nb078_alpha_dummy_020 f)),
        ((nb078_alpha_dummy_017), (nb078_alpha_dummy_019 f)), ((nb078_alpha_dummy_047),
        (nb078_alpha_dummy_048 f)), ((nb078_alpha_dummy_021), (nb078_alpha_dummy_022 f)),
        ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009),
        (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
        ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005),
        (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_032) ≠ (nb078_alpha_dummy_039) from (by
          unfold
            nb078_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0018)
                  0)))) (show (nb078_alpha_dummy_035 f) ≠ (nb078_alpha_dummy_040 f) from (by
          unfold
            nb078_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0019
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_032) ≠ (nb078_alpha_dummy_037)
        from (by
          unfold
            nb078_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0016)
                  0)))) (show (nb078_alpha_dummy_035 f) ≠ (nb078_alpha_dummy_038 f) from (by
          unfold
            nb078_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0017
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_033) ≠ (nb078_alpha_dummy_039)
        from (by
          unfold
            nb078_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0022)
                  0)))) (show (nb078_alpha_dummy_036 f) ≠ (nb078_alpha_dummy_040 f) from (by
          unfold
            nb078_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0023
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_033) ≠ (nb078_alpha_dummy_037)
        from (by
          unfold
            nb078_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0020)
                  0)))) (show (nb078_alpha_dummy_036 f) ≠ (nb078_alpha_dummy_038 f) from (by
          unfold
            nb078_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0021
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_032) ≠ (nb078_alpha_dummy_039) from (by
          unfold
            nb078_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0018)
                  0)))) (show (nb078_alpha_dummy_035 f) ≠ (nb078_alpha_dummy_040 f) from (by
          unfold
            nb078_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0019
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_032) ≠ (nb078_alpha_dummy_037)
        from (by
          unfold
            nb078_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0016)
                  0)))) (show (nb078_alpha_dummy_035 f) ≠ (nb078_alpha_dummy_038 f) from (by
          unfold
            nb078_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0017
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_033) ≠ (nb078_alpha_dummy_039)
        from (by
          unfold
            nb078_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0022)
                  0)))) (show (nb078_alpha_dummy_036 f) ≠ (nb078_alpha_dummy_040 f) from (by
          unfold
            nb078_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0023
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_033) ≠ (nb078_alpha_dummy_037)
        from (by
          unfold
            nb078_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0020)
                  0)))) (show (nb078_alpha_dummy_036 f) ≠ (nb078_alpha_dummy_038 f) from (by
          unfold
            nb078_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0021
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_033), (nb078_alpha_dummy_036 f)), ((nb078_alpha_dummy_032),
        (nb078_alpha_dummy_035 f)), ((nb078_alpha_dummy_031), (nb078_alpha_dummy_034 f)),
        ((nb078_alpha_dummy_029), (nb078_alpha_dummy_030 f)), ((nb078_alpha_dummy_025),
        (nb078_alpha_dummy_027 f)), ((nb078_alpha_dummy_026), (nb078_alpha_dummy_028 f)),
        ((nb078_alpha_dummy_051), (nb078_alpha_dummy_052 f)), ((nb078_alpha_dummy_049),
        (nb078_alpha_dummy_050 f)), ((nb078_alpha_dummy_018), (nb078_alpha_dummy_020 f)),
        ((nb078_alpha_dummy_017), (nb078_alpha_dummy_019 f)), ((nb078_alpha_dummy_047),
        (nb078_alpha_dummy_048 f)), ((nb078_alpha_dummy_021), (nb078_alpha_dummy_022 f)),
        ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009),
        (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
        ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005),
        (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_025))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_027
        f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_032) ≠ (nb078_alpha_dummy_043) from (by
          unfold
            nb078_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0026)
                  0)))) (show (nb078_alpha_dummy_035 f) ≠ (nb078_alpha_dummy_044 f) from (by
          unfold
            nb078_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0027
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_032) ≠ (nb078_alpha_dummy_041)
        from (by
          unfold
            nb078_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0024)
                  0)))) (show (nb078_alpha_dummy_035 f) ≠ (nb078_alpha_dummy_042 f) from (by
          unfold
            nb078_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0025
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_032) ≠ (nb078_alpha_dummy_043)
        from (by
          unfold
            nb078_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0026)
                  0)))) (show (nb078_alpha_dummy_035 f) ≠ (nb078_alpha_dummy_044 f) from (by
          unfold
            nb078_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0027
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_032) ≠ (nb078_alpha_dummy_041)
        from (by
          unfold
            nb078_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0024)
                  0)))) (show (nb078_alpha_dummy_035 f) ≠ (nb078_alpha_dummy_042 f) from (by
          unfold
            nb078_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0025
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_033) ≠ (nb078_alpha_dummy_045) from (by
          unfold
            nb078_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0030)
                  0)))) (show (nb078_alpha_dummy_036 f) ≠ (nb078_alpha_dummy_046 f) from (by
          unfold
            nb078_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0031
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_033) ≠ (nb078_alpha_dummy_041)
        from (by
          unfold
            nb078_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0028)
                  0)))) (show (nb078_alpha_dummy_036 f) ≠ (nb078_alpha_dummy_042 f) from (by
          unfold
            nb078_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0029
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_033) ≠
        (nb078_alpha_dummy_045) from (by
          unfold
            nb078_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0030)
                  0)))) (show (nb078_alpha_dummy_036 f) ≠ (nb078_alpha_dummy_046 f) from (by
          unfold
            nb078_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0031
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_033) ≠ (nb078_alpha_dummy_041)
        from (by
          unfold
            nb078_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0028)
                  0)))) (show (nb078_alpha_dummy_036 f) ≠ (nb078_alpha_dummy_042 f) from (by
          unfold
            nb078_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0029
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_025) ≠ (nb078_alpha_dummy_029) from (by
                                        unfold nb078_alpha_dummy_029;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0012)
                                                0)))) (show (nb078_alpha_dummy_027 f) ≠
                                        (nb078_alpha_dummy_030 f) from (by
                                        unfold nb078_alpha_dummy_030;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0013 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_029), (nb078_alpha_dummy_030 f)),
                                    ((nb078_alpha_dummy_025), (nb078_alpha_dummy_027 f)),
                                    ((nb078_alpha_dummy_026), (nb078_alpha_dummy_028 f)),
                                    ((nb078_alpha_dummy_051), (nb078_alpha_dummy_052 f)),
                                    ((nb078_alpha_dummy_049), (nb078_alpha_dummy_050 f)),
                                    ((nb078_alpha_dummy_018), (nb078_alpha_dummy_020 f)),
                                    ((nb078_alpha_dummy_017), (nb078_alpha_dummy_019 f)),
                                    ((nb078_alpha_dummy_047), (nb078_alpha_dummy_048 f)),
                                    ((nb078_alpha_dummy_021), (nb078_alpha_dummy_022 f)),
                                    ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
                                    ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
                                    ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
                                    ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
                                    ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
                                    ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_025) ≠ (nb078_alpha_dummy_029) from
                                    (by
                                      unfold nb078_alpha_dummy_029;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0012)
                                              0)))) (show
                                    (nb078_alpha_dummy_027 f) ≠ (nb078_alpha_dummy_030 f) from
                                    (by
                                      unfold nb078_alpha_dummy_030;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0013 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_025) ≠ (nb078_alpha_dummy_029) from (by
                                        unfold nb078_alpha_dummy_029;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0012)
                                                0)))) (show (nb078_alpha_dummy_027 f) ≠
                                        (nb078_alpha_dummy_030 f) from (by
                                        unfold nb078_alpha_dummy_030;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0013 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_029), (nb078_alpha_dummy_030 f)),
                                    ((nb078_alpha_dummy_025), (nb078_alpha_dummy_027 f)),
                                    ((nb078_alpha_dummy_026), (nb078_alpha_dummy_028 f)),
                                    ((nb078_alpha_dummy_051), (nb078_alpha_dummy_052 f)),
                                    ((nb078_alpha_dummy_049), (nb078_alpha_dummy_050 f)),
                                    ((nb078_alpha_dummy_018), (nb078_alpha_dummy_020 f)),
                                    ((nb078_alpha_dummy_017), (nb078_alpha_dummy_019 f)),
                                    ((nb078_alpha_dummy_047), (nb078_alpha_dummy_048 f)),
                                    ((nb078_alpha_dummy_021), (nb078_alpha_dummy_022 f)),
                                    ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
                                    ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
                                    ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
                                    ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
                                    ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
                                    ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_018) ≠ (nb078_alpha_dummy_025) from (by
                              unfold nb078_alpha_dummy_025;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0010) 0))))
                          (show (nb078_alpha_dummy_020 f) ≠ (nb078_alpha_dummy_027 f) from (by
                              unfold nb078_alpha_dummy_027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0011 f) 0))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_018) ≠ (nb078_alpha_dummy_026) from (by
                                unfold nb078_alpha_dummy_026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0010) 1))))
                            (show (nb078_alpha_dummy_020 f) ≠ (nb078_alpha_dummy_028 f) from (by
                                unfold nb078_alpha_dummy_028;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0011 f) 1))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_018) ≠ (nb078_alpha_dummy_051) from (by
                                  unfold nb078_alpha_dummy_051;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0040) 0))))
                              (show (nb078_alpha_dummy_020 f) ≠ (nb078_alpha_dummy_052 f) from
                                (by
                                  unfold nb078_alpha_dummy_052;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0041 f) 0))))
                              (TAlphaVar.there
                                (show (nb078_alpha_dummy_018) ≠ (nb078_alpha_dummy_049) from (by
                                    unfold nb078_alpha_dummy_049;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0038) 0)))) (show
                                  (nb078_alpha_dummy_020 f) ≠ (nb078_alpha_dummy_050 f) from (by
                                    unfold nb078_alpha_dummy_050;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0039 f)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_018))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_020 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_025) ≠ (nb078_alpha_dummy_032) from (by
          unfold nb078_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0014) 1)))) (show (nb078_alpha_dummy_027 f) ≠
        (nb078_alpha_dummy_035 f) from (by
          unfold nb078_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0015 f) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_025) ≠ (nb078_alpha_dummy_031) from (by
          unfold nb078_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0014) 0)))) (show (nb078_alpha_dummy_027 f) ≠
        (nb078_alpha_dummy_034 f) from (by
          unfold nb078_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0015 f) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_025) ≠ (nb078_alpha_dummy_029) from (by
          unfold nb078_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0012) 0)))) (show (nb078_alpha_dummy_027 f) ≠
        (nb078_alpha_dummy_030 f) from (by
          unfold nb078_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0013 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_033), (nb078_alpha_dummy_036 f)), ((nb078_alpha_dummy_032),
        (nb078_alpha_dummy_035 f)), ((nb078_alpha_dummy_031), (nb078_alpha_dummy_034 f)),
        ((nb078_alpha_dummy_029), (nb078_alpha_dummy_030 f)), ((nb078_alpha_dummy_025),
        (nb078_alpha_dummy_027 f)), ((nb078_alpha_dummy_026), (nb078_alpha_dummy_028 f)),
        ((nb078_alpha_dummy_051), (nb078_alpha_dummy_052 f)), ((nb078_alpha_dummy_049),
        (nb078_alpha_dummy_050 f)), ((nb078_alpha_dummy_018), (nb078_alpha_dummy_020 f)),
        ((nb078_alpha_dummy_017), (nb078_alpha_dummy_019 f)), ((nb078_alpha_dummy_047),
        (nb078_alpha_dummy_048 f)), ((nb078_alpha_dummy_021), (nb078_alpha_dummy_022 f)),
        ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009),
        (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
        ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005),
        (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_032) ≠ (nb078_alpha_dummy_039) from (by
          unfold
            nb078_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0018)
                  0)))) (show (nb078_alpha_dummy_035 f) ≠ (nb078_alpha_dummy_040 f) from (by
          unfold
            nb078_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0019
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_032) ≠ (nb078_alpha_dummy_037)
        from (by
          unfold
            nb078_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0016)
                  0)))) (show (nb078_alpha_dummy_035 f) ≠ (nb078_alpha_dummy_038 f) from (by
          unfold
            nb078_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0017
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_033) ≠ (nb078_alpha_dummy_039)
        from (by
          unfold
            nb078_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0022)
                  0)))) (show (nb078_alpha_dummy_036 f) ≠ (nb078_alpha_dummy_040 f) from (by
          unfold
            nb078_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0023
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_033) ≠ (nb078_alpha_dummy_037)
        from (by
          unfold
            nb078_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0020)
                  0)))) (show (nb078_alpha_dummy_036 f) ≠ (nb078_alpha_dummy_038 f) from (by
          unfold
            nb078_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0021
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_032) ≠ (nb078_alpha_dummy_039) from (by
          unfold
            nb078_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0018)
                  0)))) (show (nb078_alpha_dummy_035 f) ≠ (nb078_alpha_dummy_040 f) from (by
          unfold
            nb078_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0019
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_032) ≠ (nb078_alpha_dummy_037)
        from (by
          unfold
            nb078_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0016)
                  0)))) (show (nb078_alpha_dummy_035 f) ≠ (nb078_alpha_dummy_038 f) from (by
          unfold
            nb078_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0017
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_033) ≠ (nb078_alpha_dummy_039)
        from (by
          unfold
            nb078_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0022)
                  0)))) (show (nb078_alpha_dummy_036 f) ≠ (nb078_alpha_dummy_040 f) from (by
          unfold
            nb078_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0023
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_033) ≠ (nb078_alpha_dummy_037)
        from (by
          unfold
            nb078_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0020)
                  0)))) (show (nb078_alpha_dummy_036 f) ≠ (nb078_alpha_dummy_038 f) from (by
          unfold
            nb078_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0021
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_033), (nb078_alpha_dummy_036 f)), ((nb078_alpha_dummy_032),
        (nb078_alpha_dummy_035 f)), ((nb078_alpha_dummy_031), (nb078_alpha_dummy_034 f)),
        ((nb078_alpha_dummy_029), (nb078_alpha_dummy_030 f)), ((nb078_alpha_dummy_025),
        (nb078_alpha_dummy_027 f)), ((nb078_alpha_dummy_026), (nb078_alpha_dummy_028 f)),
        ((nb078_alpha_dummy_051), (nb078_alpha_dummy_052 f)), ((nb078_alpha_dummy_049),
        (nb078_alpha_dummy_050 f)), ((nb078_alpha_dummy_018), (nb078_alpha_dummy_020 f)),
        ((nb078_alpha_dummy_017), (nb078_alpha_dummy_019 f)), ((nb078_alpha_dummy_047),
        (nb078_alpha_dummy_048 f)), ((nb078_alpha_dummy_021), (nb078_alpha_dummy_022 f)),
        ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009),
        (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
        ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005),
        (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_025))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_027
        f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_032) ≠ (nb078_alpha_dummy_043) from (by
          unfold
            nb078_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0026)
                  0)))) (show (nb078_alpha_dummy_035 f) ≠ (nb078_alpha_dummy_044 f) from (by
          unfold
            nb078_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0027
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_032) ≠ (nb078_alpha_dummy_041)
        from (by
          unfold
            nb078_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0024)
                  0)))) (show (nb078_alpha_dummy_035 f) ≠ (nb078_alpha_dummy_042 f) from (by
          unfold
            nb078_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0025
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_032) ≠ (nb078_alpha_dummy_043)
        from (by
          unfold
            nb078_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0026)
                  0)))) (show (nb078_alpha_dummy_035 f) ≠ (nb078_alpha_dummy_044 f) from (by
          unfold
            nb078_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0027
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_032) ≠ (nb078_alpha_dummy_041)
        from (by
          unfold
            nb078_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0024)
                  0)))) (show (nb078_alpha_dummy_035 f) ≠ (nb078_alpha_dummy_042 f) from (by
          unfold
            nb078_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0025
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_033) ≠ (nb078_alpha_dummy_045) from (by
          unfold
            nb078_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0030)
                  0)))) (show (nb078_alpha_dummy_036 f) ≠ (nb078_alpha_dummy_046 f) from (by
          unfold
            nb078_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0031
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_033) ≠ (nb078_alpha_dummy_041)
        from (by
          unfold
            nb078_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0028)
                  0)))) (show (nb078_alpha_dummy_036 f) ≠ (nb078_alpha_dummy_042 f) from (by
          unfold
            nb078_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0029
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_033) ≠
        (nb078_alpha_dummy_045) from (by
          unfold
            nb078_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0030)
                  0)))) (show (nb078_alpha_dummy_036 f) ≠ (nb078_alpha_dummy_046 f) from (by
          unfold
            nb078_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0031
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_033) ≠ (nb078_alpha_dummy_041)
        from (by
          unfold
            nb078_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0028)
                  0)))) (show (nb078_alpha_dummy_036 f) ≠ (nb078_alpha_dummy_042 f) from (by
          unfold
            nb078_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0029
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_025) ≠ (nb078_alpha_dummy_029) from (by
                                        unfold nb078_alpha_dummy_029;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0012)
                                                0)))) (show (nb078_alpha_dummy_027 f) ≠
                                        (nb078_alpha_dummy_030 f) from (by
                                        unfold nb078_alpha_dummy_030;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0013 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_029), (nb078_alpha_dummy_030 f)),
                                    ((nb078_alpha_dummy_025), (nb078_alpha_dummy_027 f)),
                                    ((nb078_alpha_dummy_026), (nb078_alpha_dummy_028 f)),
                                    ((nb078_alpha_dummy_051), (nb078_alpha_dummy_052 f)),
                                    ((nb078_alpha_dummy_049), (nb078_alpha_dummy_050 f)),
                                    ((nb078_alpha_dummy_018), (nb078_alpha_dummy_020 f)),
                                    ((nb078_alpha_dummy_017), (nb078_alpha_dummy_019 f)),
                                    ((nb078_alpha_dummy_047), (nb078_alpha_dummy_048 f)),
                                    ((nb078_alpha_dummy_021), (nb078_alpha_dummy_022 f)),
                                    ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
                                    ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
                                    ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
                                    ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
                                    ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
                                    ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_025) ≠ (nb078_alpha_dummy_029) from
                                    (by
                                      unfold nb078_alpha_dummy_029;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0012)
                                              0)))) (show
                                    (nb078_alpha_dummy_027 f) ≠ (nb078_alpha_dummy_030 f) from
                                    (by
                                      unfold nb078_alpha_dummy_030;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0013 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_025) ≠ (nb078_alpha_dummy_029) from (by
                                        unfold nb078_alpha_dummy_029;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0012)
                                                0)))) (show (nb078_alpha_dummy_027 f) ≠
                                        (nb078_alpha_dummy_030 f) from (by
                                        unfold nb078_alpha_dummy_030;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0013 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_029), (nb078_alpha_dummy_030 f)),
                                    ((nb078_alpha_dummy_025), (nb078_alpha_dummy_027 f)),
                                    ((nb078_alpha_dummy_026), (nb078_alpha_dummy_028 f)),
                                    ((nb078_alpha_dummy_051), (nb078_alpha_dummy_052 f)),
                                    ((nb078_alpha_dummy_049), (nb078_alpha_dummy_050 f)),
                                    ((nb078_alpha_dummy_018), (nb078_alpha_dummy_020 f)),
                                    ((nb078_alpha_dummy_017), (nb078_alpha_dummy_019 f)),
                                    ((nb078_alpha_dummy_047), (nb078_alpha_dummy_048 f)),
                                    ((nb078_alpha_dummy_021), (nb078_alpha_dummy_022 f)),
                                    ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
                                    ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
                                    ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
                                    ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
                                    ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
                                    ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_049), (nb078_alpha_dummy_050 f)),
            ((nb078_alpha_dummy_018), (nb078_alpha_dummy_020 f)),
            ((nb078_alpha_dummy_017), (nb078_alpha_dummy_019 f)),
            ((nb078_alpha_dummy_047), (nb078_alpha_dummy_048 f)),
            ((nb078_alpha_dummy_021), (nb078_alpha_dummy_022 f)),
            ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
            ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
            ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
            ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
            ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
            ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
            ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part034`. -/


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
noncomputable def nb078_split_alpha_0002 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_059), (nb078_alpha_dummy_060 f)),
        ((nb078_alpha_dummy_057), (nb078_alpha_dummy_058 f)),
        ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
        ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
        ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
        ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
        ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
        ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_059))
          (Class.cab (nb078_alpha_dummy_053)
            (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_009))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_053))
                (syn_cphi (Class.cv (nb078_alpha_dummy_054))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_059)) (Class.cab (nb078_alpha_dummy_053)
              (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_009))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_053))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_054)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_060 f))
          (Class.cab (nb078_alpha_dummy_055 f)
            (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_012 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_056 f))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_060 f))
            (Class.cab (nb078_alpha_dummy_055 f)
              (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_012 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_056 f))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_009) ≠ (nb078_alpha_dummy_054) from
                    (by
                      unfold nb078_alpha_dummy_054;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0042) 1))))
                  (show (nb078_alpha_dummy_012 f) ≠ (nb078_alpha_dummy_056 f) from (by
                      unfold nb078_alpha_dummy_056;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0044 f) 1))))
                  (TAlphaVar.there (show (nb078_alpha_dummy_009) ≠ (nb078_alpha_dummy_053) from
                      (by
                        unfold nb078_alpha_dummy_053;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0042) 0))))
                    (show (nb078_alpha_dummy_012 f) ≠ (nb078_alpha_dummy_055 f) from (by
                        unfold nb078_alpha_dummy_055;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0044 f) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_009) ≠ (nb078_alpha_dummy_059) from (by
                          unfold nb078_alpha_dummy_059;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0046) 0))))
                      (show (nb078_alpha_dummy_012 f) ≠ (nb078_alpha_dummy_060 f) from (by
                          unfold nb078_alpha_dummy_060;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0047 f) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_009) ≠ (nb078_alpha_dummy_057) from (by
                            unfold nb078_alpha_dummy_057;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0043) 0))))
                        (show (nb078_alpha_dummy_012 f) ≠ (nb078_alpha_dummy_058 f) from (by
                            unfold nb078_alpha_dummy_058;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0045 f) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb078_alpha_dummy_000))).fv ∪
                              ((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv) (by decide))
                          (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv)
                            (by decide)) (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_000))).fv ∪
                                ((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_009))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_011))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_014 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_054) ≠ (nb078_alpha_dummy_061) from (by
                              unfold nb078_alpha_dummy_061;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0048) 0))))
                          (show (nb078_alpha_dummy_056 f) ≠ (nb078_alpha_dummy_063 f) from (by
                              unfold nb078_alpha_dummy_063;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0049 f) 0))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_054) ≠ (nb078_alpha_dummy_062) from (by
                                unfold nb078_alpha_dummy_062;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0048) 1))))
                            (show (nb078_alpha_dummy_056 f) ≠ (nb078_alpha_dummy_064 f) from (by
                                unfold nb078_alpha_dummy_064;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0049 f) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_054))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_056 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_061) ≠ (nb078_alpha_dummy_068) from (by
          unfold nb078_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0052) 1)))) (show (nb078_alpha_dummy_063 f) ≠
        (nb078_alpha_dummy_071 f) from (by
          unfold nb078_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0053 f) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_061) ≠ (nb078_alpha_dummy_067) from (by
          unfold nb078_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0052) 0)))) (show (nb078_alpha_dummy_063 f) ≠
        (nb078_alpha_dummy_070 f) from (by
          unfold nb078_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0053 f) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_061) ≠ (nb078_alpha_dummy_065) from (by
          unfold nb078_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0050) 0)))) (show (nb078_alpha_dummy_063 f) ≠
        (nb078_alpha_dummy_066 f) from (by
          unfold nb078_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0051 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_069), (nb078_alpha_dummy_072 f)), ((nb078_alpha_dummy_068),
        (nb078_alpha_dummy_071 f)), ((nb078_alpha_dummy_067), (nb078_alpha_dummy_070 f)),
        ((nb078_alpha_dummy_065), (nb078_alpha_dummy_066 f)), ((nb078_alpha_dummy_061),
        (nb078_alpha_dummy_063 f)), ((nb078_alpha_dummy_062), (nb078_alpha_dummy_064 f)),
        ((nb078_alpha_dummy_054), (nb078_alpha_dummy_056 f)), ((nb078_alpha_dummy_053),
        (nb078_alpha_dummy_055 f)), ((nb078_alpha_dummy_059), (nb078_alpha_dummy_060 f)),
        ((nb078_alpha_dummy_057), (nb078_alpha_dummy_058 f)), ((nb078_alpha_dummy_011),
        (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
        ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015),
        (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
        ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_068) ≠ (nb078_alpha_dummy_075) from (by
          unfold
            nb078_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0056)
                  0)))) (show (nb078_alpha_dummy_071 f) ≠ (nb078_alpha_dummy_076 f) from (by
          unfold
            nb078_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0057
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_068) ≠ (nb078_alpha_dummy_073)
        from (by
          unfold
            nb078_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0054)
                  0)))) (show (nb078_alpha_dummy_071 f) ≠ (nb078_alpha_dummy_074 f) from (by
          unfold
            nb078_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0055
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_069) ≠ (nb078_alpha_dummy_075)
        from (by
          unfold
            nb078_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0060)
                  0)))) (show (nb078_alpha_dummy_072 f) ≠ (nb078_alpha_dummy_076 f) from (by
          unfold
            nb078_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0061
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_069) ≠ (nb078_alpha_dummy_073)
        from (by
          unfold
            nb078_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0058)
                  0)))) (show (nb078_alpha_dummy_072 f) ≠ (nb078_alpha_dummy_074 f) from (by
          unfold
            nb078_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0059
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_068) ≠ (nb078_alpha_dummy_075) from (by
          unfold
            nb078_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0056)
                  0)))) (show (nb078_alpha_dummy_071 f) ≠ (nb078_alpha_dummy_076 f) from (by
          unfold
            nb078_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0057
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_068) ≠ (nb078_alpha_dummy_073)
        from (by
          unfold
            nb078_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0054)
                  0)))) (show (nb078_alpha_dummy_071 f) ≠ (nb078_alpha_dummy_074 f) from (by
          unfold
            nb078_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0055
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_069) ≠ (nb078_alpha_dummy_075)
        from (by
          unfold
            nb078_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0060)
                  0)))) (show (nb078_alpha_dummy_072 f) ≠ (nb078_alpha_dummy_076 f) from (by
          unfold
            nb078_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0061
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_069) ≠ (nb078_alpha_dummy_073)
        from (by
          unfold
            nb078_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0058)
                  0)))) (show (nb078_alpha_dummy_072 f) ≠ (nb078_alpha_dummy_074 f) from (by
          unfold
            nb078_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0059
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_069), (nb078_alpha_dummy_072 f)), ((nb078_alpha_dummy_068),
        (nb078_alpha_dummy_071 f)), ((nb078_alpha_dummy_067), (nb078_alpha_dummy_070 f)),
        ((nb078_alpha_dummy_065), (nb078_alpha_dummy_066 f)), ((nb078_alpha_dummy_061),
        (nb078_alpha_dummy_063 f)), ((nb078_alpha_dummy_062), (nb078_alpha_dummy_064 f)),
        ((nb078_alpha_dummy_054), (nb078_alpha_dummy_056 f)), ((nb078_alpha_dummy_053),
        (nb078_alpha_dummy_055 f)), ((nb078_alpha_dummy_059), (nb078_alpha_dummy_060 f)),
        ((nb078_alpha_dummy_057), (nb078_alpha_dummy_058 f)), ((nb078_alpha_dummy_011),
        (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
        ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015),
        (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
        ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_061))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_068) ≠
        (nb078_alpha_dummy_079) from (by
          unfold
            nb078_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0064)
                  0)))) (show (nb078_alpha_dummy_071 f) ≠ (nb078_alpha_dummy_080 f) from (by
          unfold
            nb078_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0065
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_068) ≠ (nb078_alpha_dummy_077)
        from (by
          unfold
            nb078_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0062)
                  0)))) (show (nb078_alpha_dummy_071 f) ≠ (nb078_alpha_dummy_078 f) from (by
          unfold
            nb078_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0063
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_068) ≠ (nb078_alpha_dummy_079)
        from (by
          unfold
            nb078_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0064)
                  0)))) (show (nb078_alpha_dummy_071 f) ≠ (nb078_alpha_dummy_080 f) from (by
          unfold
            nb078_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0065
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_068) ≠ (nb078_alpha_dummy_077)
        from (by
          unfold
            nb078_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0062)
                  0)))) (show (nb078_alpha_dummy_071 f) ≠ (nb078_alpha_dummy_078 f) from (by
          unfold
            nb078_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0063
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_069) ≠ (nb078_alpha_dummy_081) from (by
          unfold
            nb078_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0068)
                  0)))) (show (nb078_alpha_dummy_072 f) ≠ (nb078_alpha_dummy_082 f) from (by
          unfold
            nb078_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0069
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_069) ≠ (nb078_alpha_dummy_077)
        from (by
          unfold
            nb078_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0066)
                  0)))) (show (nb078_alpha_dummy_072 f) ≠ (nb078_alpha_dummy_078 f) from (by
          unfold
            nb078_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0067
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_069) ≠
        (nb078_alpha_dummy_081) from (by
          unfold
            nb078_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0068)
                  0)))) (show (nb078_alpha_dummy_072 f) ≠ (nb078_alpha_dummy_082 f) from (by
          unfold
            nb078_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0069
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_069) ≠ (nb078_alpha_dummy_077)
        from (by
          unfold
            nb078_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0066)
                  0)))) (show (nb078_alpha_dummy_072 f) ≠ (nb078_alpha_dummy_078 f) from (by
          unfold
            nb078_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0067
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_061) ≠ (nb078_alpha_dummy_065) from (by
                                        unfold nb078_alpha_dummy_065;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0050)
                                                0)))) (show (nb078_alpha_dummy_063 f) ≠
                                        (nb078_alpha_dummy_066 f) from (by
                                        unfold nb078_alpha_dummy_066;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0051 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_065), (nb078_alpha_dummy_066 f)),
                                    ((nb078_alpha_dummy_061), (nb078_alpha_dummy_063 f)),
                                    ((nb078_alpha_dummy_062), (nb078_alpha_dummy_064 f)),
                                    ((nb078_alpha_dummy_054), (nb078_alpha_dummy_056 f)),
                                    ((nb078_alpha_dummy_053), (nb078_alpha_dummy_055 f)),
                                    ((nb078_alpha_dummy_059), (nb078_alpha_dummy_060 f)),
                                    ((nb078_alpha_dummy_057), (nb078_alpha_dummy_058 f)),
                                    ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
                                    ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
                                    ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
                                    ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
                                    ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
                                    ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
                                    ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_061) ≠ (nb078_alpha_dummy_065) from
                                    (by
                                      unfold nb078_alpha_dummy_065;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0050)
                                              0)))) (show
                                    (nb078_alpha_dummy_063 f) ≠ (nb078_alpha_dummy_066 f) from
                                    (by
                                      unfold nb078_alpha_dummy_066;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0051 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_061) ≠ (nb078_alpha_dummy_065) from (by
                                        unfold nb078_alpha_dummy_065;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0050)
                                                0)))) (show (nb078_alpha_dummy_063 f) ≠
                                        (nb078_alpha_dummy_066 f) from (by
                                        unfold nb078_alpha_dummy_066;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0051 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_065), (nb078_alpha_dummy_066 f)),
                                    ((nb078_alpha_dummy_061), (nb078_alpha_dummy_063 f)),
                                    ((nb078_alpha_dummy_062), (nb078_alpha_dummy_064 f)),
                                    ((nb078_alpha_dummy_054), (nb078_alpha_dummy_056 f)),
                                    ((nb078_alpha_dummy_053), (nb078_alpha_dummy_055 f)),
                                    ((nb078_alpha_dummy_059), (nb078_alpha_dummy_060 f)),
                                    ((nb078_alpha_dummy_057), (nb078_alpha_dummy_058 f)),
                                    ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
                                    ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
                                    ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
                                    ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
                                    ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
                                    ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
                                    ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078_alpha_dummy_009) ≠ (nb078_alpha_dummy_054) from
                      (by
                        unfold nb078_alpha_dummy_054;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0042) 1))))
                    (show (nb078_alpha_dummy_012 f) ≠ (nb078_alpha_dummy_056 f) from (by
                        unfold nb078_alpha_dummy_056;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0044 f) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_009) ≠ (nb078_alpha_dummy_053) from (by
                          unfold nb078_alpha_dummy_053;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0042) 0))))
                      (show (nb078_alpha_dummy_012 f) ≠ (nb078_alpha_dummy_055 f) from (by
                          unfold nb078_alpha_dummy_055;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0044 f) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_009) ≠ (nb078_alpha_dummy_059) from (by
                            unfold nb078_alpha_dummy_059;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0046) 0))))
                        (show (nb078_alpha_dummy_012 f) ≠ (nb078_alpha_dummy_060 f) from (by
                            unfold nb078_alpha_dummy_060;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0047 f) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_009) ≠ (nb078_alpha_dummy_057) from (by
                              unfold nb078_alpha_dummy_057;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0043) 0))))
                          (show (nb078_alpha_dummy_012 f) ≠ (nb078_alpha_dummy_058 f) from (by
                              unfold nb078_alpha_dummy_058;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0045 f) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_000))).fv ∪
                                ((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (by decide))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb078_alpha_dummy_000))).fv ∪
                                  ((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (by decide))
                              (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078_alpha_dummy_009))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_011))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_014 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_054) ≠ (nb078_alpha_dummy_061) from (by
                                unfold nb078_alpha_dummy_061;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0048) 0))))
                            (show (nb078_alpha_dummy_056 f) ≠ (nb078_alpha_dummy_063 f) from (by
                                unfold nb078_alpha_dummy_063;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0049 f) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_054) ≠ (nb078_alpha_dummy_062) from (by
                                  unfold nb078_alpha_dummy_062;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0048) 1))))
                              (show (nb078_alpha_dummy_056 f) ≠ (nb078_alpha_dummy_064 f) from
                                (by
                                  unfold nb078_alpha_dummy_064;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0049 f) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_054))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_056 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_061) ≠ (nb078_alpha_dummy_068) from (by
          unfold nb078_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0052) 1)))) (show (nb078_alpha_dummy_063 f) ≠
        (nb078_alpha_dummy_071 f) from (by
          unfold nb078_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0053 f) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_061) ≠ (nb078_alpha_dummy_067) from (by
          unfold nb078_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0052) 0)))) (show (nb078_alpha_dummy_063 f) ≠
        (nb078_alpha_dummy_070 f) from (by
          unfold nb078_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0053 f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_061) ≠ (nb078_alpha_dummy_065)
        from (by
          unfold nb078_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0050)
                  0)))) (show (nb078_alpha_dummy_063 f) ≠ (nb078_alpha_dummy_066 f) from (by
          unfold nb078_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0051 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_069), (nb078_alpha_dummy_072 f)), ((nb078_alpha_dummy_068),
        (nb078_alpha_dummy_071 f)), ((nb078_alpha_dummy_067), (nb078_alpha_dummy_070 f)),
        ((nb078_alpha_dummy_065), (nb078_alpha_dummy_066 f)), ((nb078_alpha_dummy_061),
        (nb078_alpha_dummy_063 f)), ((nb078_alpha_dummy_062), (nb078_alpha_dummy_064 f)),
        ((nb078_alpha_dummy_054), (nb078_alpha_dummy_056 f)), ((nb078_alpha_dummy_053),
        (nb078_alpha_dummy_055 f)), ((nb078_alpha_dummy_059), (nb078_alpha_dummy_060 f)),
        ((nb078_alpha_dummy_057), (nb078_alpha_dummy_058 f)), ((nb078_alpha_dummy_011),
        (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
        ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015),
        (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
        ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_068) ≠ (nb078_alpha_dummy_075) from (by
          unfold
            nb078_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0056)
                  0)))) (show (nb078_alpha_dummy_071 f) ≠ (nb078_alpha_dummy_076 f) from (by
          unfold
            nb078_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0057
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_068) ≠ (nb078_alpha_dummy_073)
        from (by
          unfold
            nb078_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0054)
                  0)))) (show (nb078_alpha_dummy_071 f) ≠ (nb078_alpha_dummy_074 f) from (by
          unfold
            nb078_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0055
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_069) ≠ (nb078_alpha_dummy_075)
        from (by
          unfold
            nb078_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0060)
                  0)))) (show (nb078_alpha_dummy_072 f) ≠ (nb078_alpha_dummy_076 f) from (by
          unfold
            nb078_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0061
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_069) ≠ (nb078_alpha_dummy_073)
        from (by
          unfold
            nb078_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0058)
                  0)))) (show (nb078_alpha_dummy_072 f) ≠ (nb078_alpha_dummy_074 f) from (by
          unfold
            nb078_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0059
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_068) ≠ (nb078_alpha_dummy_075) from (by
          unfold
            nb078_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0056)
                  0)))) (show (nb078_alpha_dummy_071 f) ≠ (nb078_alpha_dummy_076 f) from (by
          unfold
            nb078_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0057
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_068) ≠ (nb078_alpha_dummy_073)
        from (by
          unfold
            nb078_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0054)
                  0)))) (show (nb078_alpha_dummy_071 f) ≠ (nb078_alpha_dummy_074 f) from (by
          unfold
            nb078_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0055
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_069) ≠ (nb078_alpha_dummy_075)
        from (by
          unfold
            nb078_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0060)
                  0)))) (show (nb078_alpha_dummy_072 f) ≠ (nb078_alpha_dummy_076 f) from (by
          unfold
            nb078_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0061
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_069) ≠ (nb078_alpha_dummy_073)
        from (by
          unfold
            nb078_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0058)
                  0)))) (show (nb078_alpha_dummy_072 f) ≠ (nb078_alpha_dummy_074 f) from (by
          unfold
            nb078_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0059
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_069), (nb078_alpha_dummy_072 f)), ((nb078_alpha_dummy_068),
        (nb078_alpha_dummy_071 f)), ((nb078_alpha_dummy_067), (nb078_alpha_dummy_070 f)),
        ((nb078_alpha_dummy_065), (nb078_alpha_dummy_066 f)), ((nb078_alpha_dummy_061),
        (nb078_alpha_dummy_063 f)), ((nb078_alpha_dummy_062), (nb078_alpha_dummy_064 f)),
        ((nb078_alpha_dummy_054), (nb078_alpha_dummy_056 f)), ((nb078_alpha_dummy_053),
        (nb078_alpha_dummy_055 f)), ((nb078_alpha_dummy_059), (nb078_alpha_dummy_060 f)),
        ((nb078_alpha_dummy_057), (nb078_alpha_dummy_058 f)), ((nb078_alpha_dummy_011),
        (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
        ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015),
        (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
        ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_061))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_063
        f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_068) ≠
        (nb078_alpha_dummy_079) from (by
          unfold
            nb078_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0064)
                  0)))) (show (nb078_alpha_dummy_071 f) ≠ (nb078_alpha_dummy_080 f) from (by
          unfold
            nb078_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0065
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_068) ≠ (nb078_alpha_dummy_077)
        from (by
          unfold
            nb078_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0062)
                  0)))) (show (nb078_alpha_dummy_071 f) ≠ (nb078_alpha_dummy_078 f) from (by
          unfold
            nb078_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0063
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_068) ≠ (nb078_alpha_dummy_079)
        from (by
          unfold
            nb078_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0064)
                  0)))) (show (nb078_alpha_dummy_071 f) ≠ (nb078_alpha_dummy_080 f) from (by
          unfold
            nb078_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0065
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_068) ≠ (nb078_alpha_dummy_077)
        from (by
          unfold
            nb078_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0062)
                  0)))) (show (nb078_alpha_dummy_071 f) ≠ (nb078_alpha_dummy_078 f) from (by
          unfold
            nb078_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0063
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_069) ≠ (nb078_alpha_dummy_081) from (by
          unfold
            nb078_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0068)
                  0)))) (show (nb078_alpha_dummy_072 f) ≠ (nb078_alpha_dummy_082 f) from (by
          unfold
            nb078_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0069
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_069) ≠ (nb078_alpha_dummy_077)
        from (by
          unfold
            nb078_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0066)
                  0)))) (show (nb078_alpha_dummy_072 f) ≠ (nb078_alpha_dummy_078 f) from (by
          unfold
            nb078_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0067
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_069) ≠
        (nb078_alpha_dummy_081) from (by
          unfold
            nb078_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0068)
                  0)))) (show (nb078_alpha_dummy_072 f) ≠ (nb078_alpha_dummy_082 f) from (by
          unfold
            nb078_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0069
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_069) ≠ (nb078_alpha_dummy_077)
        from (by
          unfold
            nb078_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0066)
                  0)))) (show (nb078_alpha_dummy_072 f) ≠ (nb078_alpha_dummy_078 f) from (by
          unfold
            nb078_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0067
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_061) ≠ (nb078_alpha_dummy_065) from
                                        (by
                                          unfold nb078_alpha_dummy_065;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0050)
                                                  0)))) (show (nb078_alpha_dummy_063 f) ≠
        (nb078_alpha_dummy_066 f) from (by
                                          unfold nb078_alpha_dummy_066;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0051 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_065), (nb078_alpha_dummy_066 f)),
                                      ((nb078_alpha_dummy_061), (nb078_alpha_dummy_063 f)),
                                      ((nb078_alpha_dummy_062), (nb078_alpha_dummy_064 f)),
                                      ((nb078_alpha_dummy_054), (nb078_alpha_dummy_056 f)),
                                      ((nb078_alpha_dummy_053), (nb078_alpha_dummy_055 f)),
                                      ((nb078_alpha_dummy_059), (nb078_alpha_dummy_060 f)),
                                      ((nb078_alpha_dummy_057), (nb078_alpha_dummy_058 f)),
                                      ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
                                      ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
                                      ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
                                      ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
                                      ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
                                      ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
                                      ((nb078_alpha_dummy_000), f),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_061) ≠ (nb078_alpha_dummy_065) from (by
                                        unfold nb078_alpha_dummy_065;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0050)
                                                0)))) (show (nb078_alpha_dummy_063 f) ≠
                                        (nb078_alpha_dummy_066 f) from (by
                                        unfold nb078_alpha_dummy_066;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0051 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_061) ≠ (nb078_alpha_dummy_065) from
                                        (by
                                          unfold nb078_alpha_dummy_065;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0050)
                                                  0)))) (show (nb078_alpha_dummy_063 f) ≠
        (nb078_alpha_dummy_066 f) from (by
                                          unfold nb078_alpha_dummy_066;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0051 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_065), (nb078_alpha_dummy_066 f)),
                                      ((nb078_alpha_dummy_061), (nb078_alpha_dummy_063 f)),
                                      ((nb078_alpha_dummy_062), (nb078_alpha_dummy_064 f)),
                                      ((nb078_alpha_dummy_054), (nb078_alpha_dummy_056 f)),
                                      ((nb078_alpha_dummy_053), (nb078_alpha_dummy_055 f)),
                                      ((nb078_alpha_dummy_059), (nb078_alpha_dummy_060 f)),
                                      ((nb078_alpha_dummy_057), (nb078_alpha_dummy_058 f)),
                                      ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
                                      ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
                                      ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
                                      ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
                                      ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
                                      ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
                                      ((nb078_alpha_dummy_000), f),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
