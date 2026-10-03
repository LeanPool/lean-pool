/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C076C001Part005

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C076C001Part006`. -/


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
noncomputable def nb076_split_alpha_0000 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var)
    (dv_m_n : m ≠ n) :
    TAlphaWff
      [((nb076_alpha_dummy_023), (nb076_alpha_dummy_024 m n)),
        ((nb076_alpha_dummy_021), (nb076_alpha_dummy_022 m n)),
        ((nb076_alpha_dummy_010), (nb076_alpha_dummy_012 g m n a b)),
        ((nb076_alpha_dummy_009), (nb076_alpha_dummy_011 g m n a b)),
        ((nb076_alpha_dummy_015), (nb076_alpha_dummy_016 g m n a b)),
        ((nb076_alpha_dummy_013), (nb076_alpha_dummy_014 g m n a b)),
        ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)),
        ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m),
        ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))]
      (Wff.imp (Wff.classMem (Class.cv (nb076_alpha_dummy_023))
          (Class.cab (nb076_alpha_dummy_017)
            (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_017))
                (syn_cphi (Class.cv (nb076_alpha_dummy_018))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb076_alpha_dummy_023)) (Class.cab (nb076_alpha_dummy_017)
              (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_003))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_017))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_018)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb076_alpha_dummy_024 m n))
          (Class.cab (nb076_alpha_dummy_019 m n)
            (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv m)
              (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n))
                (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb076_alpha_dummy_024 m n))
            (Class.cab (nb076_alpha_dummy_019 m n)
              (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv m)
                (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb076_alpha_dummy_003) ≠ (nb076_alpha_dummy_018) from
                    (by
                      unfold nb076_alpha_dummy_018;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0014) 1))))
                  (show m ≠ (nb076_alpha_dummy_020 m n) from (by
                      unfold nb076_alpha_dummy_020;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb076_support_mem_0016 m n) 1)))) (TAlphaVar.there
                    (show (nb076_alpha_dummy_003) ≠ (nb076_alpha_dummy_017) from (by
                        unfold nb076_alpha_dummy_017;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0014) 0))))
                    (show m ≠ (nb076_alpha_dummy_019 m n) from (by
                        unfold nb076_alpha_dummy_019;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb076_support_mem_0016 m n) 0))))
                    (TAlphaVar.there
                      (show (nb076_alpha_dummy_003) ≠ (nb076_alpha_dummy_023) from (by
                          unfold nb076_alpha_dummy_023;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb076_support_mem_0018) 0))))
                      (show m ≠ (nb076_alpha_dummy_024 m n) from (by
                          unfold nb076_alpha_dummy_024;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb076_support_mem_0019 m n) 0))))
                      (TAlphaVar.there
                        (show (nb076_alpha_dummy_003) ≠ (nb076_alpha_dummy_021) from (by
                            unfold nb076_alpha_dummy_021;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb076_support_mem_0015) 0))))
                        (show m ≠ (nb076_alpha_dummy_022 m n) from (by
                            unfold nb076_alpha_dummy_022;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb076_support_mem_0017 m n) 0))))
                        (TAlphaVar.there
                          (show (nb076_alpha_dummy_003) ≠ (nb076_alpha_dummy_010) from (by
                              unfold nb076_alpha_dummy_010;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0008) 1))))
                          (show m ≠ (nb076_alpha_dummy_012 g m n a b) from (by
                              unfold nb076_alpha_dummy_012;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0010 g m n a b)
                                      1)))) (TAlphaVar.there
                            (show (nb076_alpha_dummy_003) ≠ (nb076_alpha_dummy_009) from (by
                                unfold nb076_alpha_dummy_009;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0008) 0))))
                            (show m ≠ (nb076_alpha_dummy_011 g m n a b) from (by
                                unfold nb076_alpha_dummy_011;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0010 g m n a b)
                                        0)))) (TAlphaVar.there
                              (show (nb076_alpha_dummy_003) ≠ (nb076_alpha_dummy_015) from (by
                                  unfold nb076_alpha_dummy_015;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb076_support_mem_0012) 0))))
                              (show m ≠ (nb076_alpha_dummy_016 g m n a b) from (by
                                  unfold nb076_alpha_dummy_016;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb076_support_mem_0013 g m n a b) 0))))
                              (TAlphaVar.there
                                (show (nb076_alpha_dummy_003) ≠ (nb076_alpha_dummy_013) from (by
                                    unfold nb076_alpha_dummy_013;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb076_support_mem_0009) 0))))
                                (show m ≠ (nb076_alpha_dummy_014 g m n a b) from (by
                                    unfold nb076_alpha_dummy_014;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb076_support_mem_0011 g m n a b) 0))))
                                (TAlphaVar.there
                                  (show (nb076_alpha_dummy_003) ≠ (nb076_alpha_dummy_005) from
                                    (by
                                      unfold nb076_alpha_dummy_005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb076_support_mem_0006)
                                              0))))
                                  (show m ≠ (nb076_alpha_dummy_006 g m n a b) from (by
                                      unfold nb076_alpha_dummy_006;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb076_support_mem_0007 g m n a b) 0))))
                                  (TAlphaVar.there
                                    (freshVar_injective ((∅ : Finset Var)) (by decide))
                                    dv_m_n (TAlphaVar.here _ _ _))))))))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb076_alpha_dummy_003))).fv ∪
                      ((Class.cv (nb076_alpha_dummy_004))).fv) (by decide))
                  (freshVar_injective (((Class.cv m)).fv ∪ ((Class.cv n)).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb076_alpha_dummy_018) ≠ (nb076_alpha_dummy_025) from (by
                              unfold nb076_alpha_dummy_025;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0020) 0))))
                          (show (nb076_alpha_dummy_020 m n) ≠ (nb076_alpha_dummy_027 m n) from
                            (by
                              unfold nb076_alpha_dummy_027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0021 m n) 0))))
                          (TAlphaVar.there
                            (show (nb076_alpha_dummy_018) ≠ (nb076_alpha_dummy_026) from (by
                                unfold nb076_alpha_dummy_026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0020) 1)))) (show
                              (nb076_alpha_dummy_020 m n) ≠ (nb076_alpha_dummy_028 m n) from (by
                                unfold nb076_alpha_dummy_028;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0021 m n) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb076_alpha_dummy_018))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv (nb076_alpha_dummy_020 m n))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_025) ≠ (nb076_alpha_dummy_032) from (by
          unfold nb076_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0024) 1)))) (show (nb076_alpha_dummy_027 m n) ≠
        (nb076_alpha_dummy_035 m n) from (by
          unfold nb076_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0025 m n) 1)))) (TAlphaVar.there (show
        (nb076_alpha_dummy_025) ≠ (nb076_alpha_dummy_031) from (by
          unfold nb076_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0024) 0)))) (show (nb076_alpha_dummy_027 m n) ≠
        (nb076_alpha_dummy_034 m n) from (by
          unfold nb076_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0025 m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_025) ≠ (nb076_alpha_dummy_029)
        from (by
          unfold nb076_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0022) 0)))) (show (nb076_alpha_dummy_027 m n) ≠
        (nb076_alpha_dummy_030 m n) from (by
          unfold nb076_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0023 m n)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb076_alpha_dummy_033), (nb076_alpha_dummy_036 m n)), ((nb076_alpha_dummy_032),
        (nb076_alpha_dummy_035 m n)), ((nb076_alpha_dummy_031), (nb076_alpha_dummy_034 m n)),
        ((nb076_alpha_dummy_029), (nb076_alpha_dummy_030 m n)), ((nb076_alpha_dummy_025),
        (nb076_alpha_dummy_027 m n)), ((nb076_alpha_dummy_026), (nb076_alpha_dummy_028 m n)),
        ((nb076_alpha_dummy_018), (nb076_alpha_dummy_020 m n)), ((nb076_alpha_dummy_017),
        (nb076_alpha_dummy_019 m n)), ((nb076_alpha_dummy_023), (nb076_alpha_dummy_024 m n)),
        ((nb076_alpha_dummy_021), (nb076_alpha_dummy_022 m n)), ((nb076_alpha_dummy_010),
        (nb076_alpha_dummy_012 g m n a b)), ((nb076_alpha_dummy_009),
        (nb076_alpha_dummy_011 g m n a b)), ((nb076_alpha_dummy_015),
        (nb076_alpha_dummy_016 g m n a b)), ((nb076_alpha_dummy_013),
        (nb076_alpha_dummy_014 g m n a b)), ((nb076_alpha_dummy_005),
        (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n),
        ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007),
        (nb076_alpha_dummy_008 g m n a b))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_032) ≠
        (nb076_alpha_dummy_039) from (by
          unfold
            nb076_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0028)
                  0)))) (show (nb076_alpha_dummy_035 m n) ≠ (nb076_alpha_dummy_040 m n) from (by
          unfold
            nb076_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0029
                    m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_032) ≠ (nb076_alpha_dummy_037)
        from (by
          unfold
            nb076_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0026)
                  0)))) (show (nb076_alpha_dummy_035 m n) ≠ (nb076_alpha_dummy_038 m n) from (by
          unfold
            nb076_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0027
                    m n)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_033) ≠ (nb076_alpha_dummy_039)
        from (by
          unfold
            nb076_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0032)
                  0)))) (show (nb076_alpha_dummy_036 m n) ≠ (nb076_alpha_dummy_040 m n) from (by
          unfold
            nb076_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0033
                    m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_033) ≠ (nb076_alpha_dummy_037)
        from (by
          unfold
            nb076_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0030)
                  0)))) (show (nb076_alpha_dummy_036 m n) ≠ (nb076_alpha_dummy_038 m n) from (by
          unfold
            nb076_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0031
                    m n)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_032) ≠ (nb076_alpha_dummy_039) from (by
          unfold
            nb076_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0028)
                  0)))) (show (nb076_alpha_dummy_035 m n) ≠ (nb076_alpha_dummy_040 m n) from (by
          unfold
            nb076_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0029
                    m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_032) ≠ (nb076_alpha_dummy_037)
        from (by
          unfold
            nb076_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0026)
                  0)))) (show (nb076_alpha_dummy_035 m n) ≠ (nb076_alpha_dummy_038 m n) from (by
          unfold
            nb076_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0027
                    m n)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_033) ≠ (nb076_alpha_dummy_039)
        from (by
          unfold
            nb076_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0032)
                  0)))) (show (nb076_alpha_dummy_036 m n) ≠ (nb076_alpha_dummy_040 m n) from (by
          unfold
            nb076_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0033
                    m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_033) ≠ (nb076_alpha_dummy_037)
        from (by
          unfold
            nb076_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0030)
                  0)))) (show (nb076_alpha_dummy_036 m n) ≠ (nb076_alpha_dummy_038 m n) from (by
          unfold
            nb076_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0031
                    m n)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb076_alpha_dummy_033), (nb076_alpha_dummy_036 m n)), ((nb076_alpha_dummy_032),
        (nb076_alpha_dummy_035 m n)), ((nb076_alpha_dummy_031), (nb076_alpha_dummy_034 m n)),
        ((nb076_alpha_dummy_029), (nb076_alpha_dummy_030 m n)), ((nb076_alpha_dummy_025),
        (nb076_alpha_dummy_027 m n)), ((nb076_alpha_dummy_026), (nb076_alpha_dummy_028 m n)),
        ((nb076_alpha_dummy_018), (nb076_alpha_dummy_020 m n)), ((nb076_alpha_dummy_017),
        (nb076_alpha_dummy_019 m n)), ((nb076_alpha_dummy_023), (nb076_alpha_dummy_024 m n)),
        ((nb076_alpha_dummy_021), (nb076_alpha_dummy_022 m n)), ((nb076_alpha_dummy_010),
        (nb076_alpha_dummy_012 g m n a b)), ((nb076_alpha_dummy_009),
        (nb076_alpha_dummy_011 g m n a b)), ((nb076_alpha_dummy_015),
        (nb076_alpha_dummy_016 g m n a b)), ((nb076_alpha_dummy_013),
        (nb076_alpha_dummy_014 g m n a b)), ((nb076_alpha_dummy_005),
        (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n),
        ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007),
        (nb076_alpha_dummy_008 g m n a b))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_025))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_027 m
        n))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_032) ≠ (nb076_alpha_dummy_043) from (by
          unfold
            nb076_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0036)
                  0)))) (show (nb076_alpha_dummy_035 m n) ≠ (nb076_alpha_dummy_044 m n) from (by
          unfold
            nb076_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0037
                    m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_032) ≠ (nb076_alpha_dummy_041)
        from (by
          unfold
            nb076_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0034)
                  0)))) (show (nb076_alpha_dummy_035 m n) ≠ (nb076_alpha_dummy_042 m n) from (by
          unfold
            nb076_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0035
                    m n)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_032) ≠ (nb076_alpha_dummy_043)
        from (by
          unfold
            nb076_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0036)
                  0)))) (show (nb076_alpha_dummy_035 m n) ≠ (nb076_alpha_dummy_044 m n) from (by
          unfold
            nb076_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0037
                    m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_032) ≠ (nb076_alpha_dummy_041)
        from (by
          unfold
            nb076_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0034)
                  0)))) (show (nb076_alpha_dummy_035 m n) ≠ (nb076_alpha_dummy_042 m n) from (by
          unfold
            nb076_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0035
                    m n)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_033) ≠ (nb076_alpha_dummy_045) from (by
          unfold
            nb076_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0040)
                  0)))) (show (nb076_alpha_dummy_036 m n) ≠ (nb076_alpha_dummy_046 m n) from (by
          unfold
            nb076_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0041
                    m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_033) ≠ (nb076_alpha_dummy_041)
        from (by
          unfold
            nb076_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0038)
                  0)))) (show (nb076_alpha_dummy_036 m n) ≠ (nb076_alpha_dummy_042 m n) from (by
          unfold
            nb076_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0039
                    m n)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_033) ≠
        (nb076_alpha_dummy_045) from (by
          unfold
            nb076_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0040)
                  0)))) (show (nb076_alpha_dummy_036 m n) ≠ (nb076_alpha_dummy_046 m n) from (by
          unfold
            nb076_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0041
                    m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_033) ≠ (nb076_alpha_dummy_041)
        from (by
          unfold
            nb076_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0038)
                  0)))) (show (nb076_alpha_dummy_036 m n) ≠ (nb076_alpha_dummy_042 m n) from (by
          unfold
            nb076_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0039
                    m n)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb076_alpha_dummy_025) ≠ (nb076_alpha_dummy_029) from (by
                                        unfold nb076_alpha_dummy_029;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0022)
                                                0)))) (show (nb076_alpha_dummy_027 m n) ≠
                                        (nb076_alpha_dummy_030 m n) from (by
                                        unfold nb076_alpha_dummy_030;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0023 m n) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb076_alpha_dummy_029), (nb076_alpha_dummy_030 m n)),
                                    ((nb076_alpha_dummy_025), (nb076_alpha_dummy_027 m n)),
                                    ((nb076_alpha_dummy_026), (nb076_alpha_dummy_028 m n)),
                                    ((nb076_alpha_dummy_018), (nb076_alpha_dummy_020 m n)),
                                    ((nb076_alpha_dummy_017), (nb076_alpha_dummy_019 m n)),
                                    ((nb076_alpha_dummy_023), (nb076_alpha_dummy_024 m n)),
                                    ((nb076_alpha_dummy_021), (nb076_alpha_dummy_022 m n)),
                                    ((nb076_alpha_dummy_010),
                                      (nb076_alpha_dummy_012 g m n a b)),
                                    ((nb076_alpha_dummy_009),
                                      (nb076_alpha_dummy_011 g m n a b)),
                                    ((nb076_alpha_dummy_015),
                                      (nb076_alpha_dummy_016 g m n a b)),
                                    ((nb076_alpha_dummy_013),
                                      (nb076_alpha_dummy_014 g m n a b)),
                                    ((nb076_alpha_dummy_005),
                                      (nb076_alpha_dummy_006 g m n a b)),
                                    ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m),
                                    ((nb076_alpha_dummy_007),
                                      (nb076_alpha_dummy_008 g m n a b))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb076_alpha_dummy_025) ≠ (nb076_alpha_dummy_029) from
                                    (by
                                      unfold nb076_alpha_dummy_029;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb076_support_mem_0022)
                                              0)))) (show (nb076_alpha_dummy_027 m n) ≠
                                      (nb076_alpha_dummy_030 m n) from (by
                                      unfold nb076_alpha_dummy_030;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb076_support_mem_0023 m n)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb076_alpha_dummy_025) ≠ (nb076_alpha_dummy_029) from (by
                                        unfold nb076_alpha_dummy_029;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0022)
                                                0)))) (show (nb076_alpha_dummy_027 m n) ≠
                                        (nb076_alpha_dummy_030 m n) from (by
                                        unfold nb076_alpha_dummy_030;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0023 m n) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb076_alpha_dummy_029), (nb076_alpha_dummy_030 m n)),
                                    ((nb076_alpha_dummy_025), (nb076_alpha_dummy_027 m n)),
                                    ((nb076_alpha_dummy_026), (nb076_alpha_dummy_028 m n)),
                                    ((nb076_alpha_dummy_018), (nb076_alpha_dummy_020 m n)),
                                    ((nb076_alpha_dummy_017), (nb076_alpha_dummy_019 m n)),
                                    ((nb076_alpha_dummy_023), (nb076_alpha_dummy_024 m n)),
                                    ((nb076_alpha_dummy_021), (nb076_alpha_dummy_022 m n)),
                                    ((nb076_alpha_dummy_010),
                                      (nb076_alpha_dummy_012 g m n a b)),
                                    ((nb076_alpha_dummy_009),
                                      (nb076_alpha_dummy_011 g m n a b)),
                                    ((nb076_alpha_dummy_015),
                                      (nb076_alpha_dummy_016 g m n a b)),
                                    ((nb076_alpha_dummy_013),
                                      (nb076_alpha_dummy_014 g m n a b)),
                                    ((nb076_alpha_dummy_005),
                                      (nb076_alpha_dummy_006 g m n a b)),
                                    ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m),
                                    ((nb076_alpha_dummy_007),
                                      (nb076_alpha_dummy_008 g m n a b))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb076_alpha_dummy_003) ≠ (nb076_alpha_dummy_018) from
                      (by
                        unfold nb076_alpha_dummy_018;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0014) 1))))
                    (show m ≠ (nb076_alpha_dummy_020 m n) from (by
                        unfold nb076_alpha_dummy_020;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb076_support_mem_0016 m n) 1))))
                    (TAlphaVar.there
                      (show (nb076_alpha_dummy_003) ≠ (nb076_alpha_dummy_017) from (by
                          unfold nb076_alpha_dummy_017;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb076_support_mem_0014) 0))))
                      (show m ≠ (nb076_alpha_dummy_019 m n) from (by
                          unfold nb076_alpha_dummy_019;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb076_support_mem_0016 m n) 0))))
                      (TAlphaVar.there
                        (show (nb076_alpha_dummy_003) ≠ (nb076_alpha_dummy_023) from (by
                            unfold nb076_alpha_dummy_023;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb076_support_mem_0018) 0))))
                        (show m ≠ (nb076_alpha_dummy_024 m n) from (by
                            unfold nb076_alpha_dummy_024;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb076_support_mem_0019 m n) 0))))
                        (TAlphaVar.there
                          (show (nb076_alpha_dummy_003) ≠ (nb076_alpha_dummy_021) from (by
                              unfold nb076_alpha_dummy_021;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0015) 0))))
                          (show m ≠ (nb076_alpha_dummy_022 m n) from (by
                              unfold nb076_alpha_dummy_022;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0017 m n) 0))))
                          (TAlphaVar.there
                            (show (nb076_alpha_dummy_003) ≠ (nb076_alpha_dummy_010) from (by
                                unfold nb076_alpha_dummy_010;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0008) 1))))
                            (show m ≠ (nb076_alpha_dummy_012 g m n a b) from (by
                                unfold nb076_alpha_dummy_012;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0010 g m n a b)
                                        1)))) (TAlphaVar.there
                              (show (nb076_alpha_dummy_003) ≠ (nb076_alpha_dummy_009) from (by
                                  unfold nb076_alpha_dummy_009;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb076_support_mem_0008) 0))))
                              (show m ≠ (nb076_alpha_dummy_011 g m n a b) from (by
                                  unfold nb076_alpha_dummy_011;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb076_support_mem_0010 g m n a b) 0))))
                              (TAlphaVar.there
                                (show (nb076_alpha_dummy_003) ≠ (nb076_alpha_dummy_015) from (by
                                    unfold nb076_alpha_dummy_015;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb076_support_mem_0012) 0))))
                                (show m ≠ (nb076_alpha_dummy_016 g m n a b) from (by
                                    unfold nb076_alpha_dummy_016;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb076_support_mem_0013 g m n a b) 0))))
                                (TAlphaVar.there
                                  (show (nb076_alpha_dummy_003) ≠ (nb076_alpha_dummy_013) from
                                    (by
                                      unfold nb076_alpha_dummy_013;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb076_support_mem_0009)
                                              0))))
                                  (show m ≠ (nb076_alpha_dummy_014 g m n a b) from (by
                                      unfold nb076_alpha_dummy_014;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb076_support_mem_0011 g m n a b) 0))))
                                  (TAlphaVar.there (show
                                      (nb076_alpha_dummy_003) ≠ (nb076_alpha_dummy_005) from (by
                                        unfold nb076_alpha_dummy_005;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0006)
                                                0))))
                                    (show m ≠ (nb076_alpha_dummy_006 g m n a b) from (by
                                        unfold nb076_alpha_dummy_006;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0007 g m n a b) 0))))
                                    (TAlphaVar.there
                                      (freshVar_injective ((∅ : Finset Var)) (by decide))
                                      dv_m_n (TAlphaVar.here _ _ _)))))))))))))
              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb076_alpha_dummy_003))).fv ∪
                        ((Class.cv (nb076_alpha_dummy_004))).fv) (by decide))
                    (freshVar_injective (((Class.cv m)).fv ∪ ((Class.cv n)).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb076_alpha_dummy_018) ≠ (nb076_alpha_dummy_025) from (by
                                unfold nb076_alpha_dummy_025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0020) 0)))) (show
                              (nb076_alpha_dummy_020 m n) ≠ (nb076_alpha_dummy_027 m n) from (by
                                unfold nb076_alpha_dummy_027;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0021 m n) 0))))
                            (TAlphaVar.there
                              (show (nb076_alpha_dummy_018) ≠ (nb076_alpha_dummy_026) from (by
                                  unfold nb076_alpha_dummy_026;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb076_support_mem_0020) 1)))) (show
                                (nb076_alpha_dummy_020 m n) ≠ (nb076_alpha_dummy_028 m n) from
                                (by
                                  unfold nb076_alpha_dummy_028;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb076_support_mem_0021 m n)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb076_alpha_dummy_018))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb076_alpha_dummy_020 m n))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb076_alpha_dummy_025) ≠ (nb076_alpha_dummy_032) from (by
          unfold nb076_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0024) 1)))) (show (nb076_alpha_dummy_027 m n) ≠
        (nb076_alpha_dummy_035 m n) from (by
          unfold nb076_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0025 m n)
                  1)))) (TAlphaVar.there (show (nb076_alpha_dummy_025) ≠ (nb076_alpha_dummy_031)
        from (by
          unfold nb076_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0024) 0)))) (show (nb076_alpha_dummy_027 m n) ≠
        (nb076_alpha_dummy_034 m n) from (by
          unfold nb076_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0025 m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_025) ≠ (nb076_alpha_dummy_029)
        from (by
          unfold nb076_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0022)
                  0)))) (show (nb076_alpha_dummy_027 m n) ≠ (nb076_alpha_dummy_030 m n) from (by
          unfold nb076_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0023 m n)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb076_alpha_dummy_033), (nb076_alpha_dummy_036 m n)), ((nb076_alpha_dummy_032),
        (nb076_alpha_dummy_035 m n)), ((nb076_alpha_dummy_031), (nb076_alpha_dummy_034 m n)),
        ((nb076_alpha_dummy_029), (nb076_alpha_dummy_030 m n)), ((nb076_alpha_dummy_025),
        (nb076_alpha_dummy_027 m n)), ((nb076_alpha_dummy_026), (nb076_alpha_dummy_028 m n)),
        ((nb076_alpha_dummy_018), (nb076_alpha_dummy_020 m n)), ((nb076_alpha_dummy_017),
        (nb076_alpha_dummy_019 m n)), ((nb076_alpha_dummy_023), (nb076_alpha_dummy_024 m n)),
        ((nb076_alpha_dummy_021), (nb076_alpha_dummy_022 m n)), ((nb076_alpha_dummy_010),
        (nb076_alpha_dummy_012 g m n a b)), ((nb076_alpha_dummy_009),
        (nb076_alpha_dummy_011 g m n a b)), ((nb076_alpha_dummy_015),
        (nb076_alpha_dummy_016 g m n a b)), ((nb076_alpha_dummy_013),
        (nb076_alpha_dummy_014 g m n a b)), ((nb076_alpha_dummy_005),
        (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n),
        ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007),
        (nb076_alpha_dummy_008 g m n a b))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_032) ≠
        (nb076_alpha_dummy_039) from (by
          unfold
            nb076_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0028)
                  0)))) (show (nb076_alpha_dummy_035 m n) ≠ (nb076_alpha_dummy_040 m n) from (by
          unfold
            nb076_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0029
                    m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_032) ≠ (nb076_alpha_dummy_037)
        from (by
          unfold
            nb076_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0026)
                  0)))) (show (nb076_alpha_dummy_035 m n) ≠ (nb076_alpha_dummy_038 m n) from (by
          unfold
            nb076_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0027
                    m n)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_033) ≠ (nb076_alpha_dummy_039)
        from (by
          unfold
            nb076_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0032)
                  0)))) (show (nb076_alpha_dummy_036 m n) ≠ (nb076_alpha_dummy_040 m n) from (by
          unfold
            nb076_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0033
                    m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_033) ≠ (nb076_alpha_dummy_037)
        from (by
          unfold
            nb076_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0030)
                  0)))) (show (nb076_alpha_dummy_036 m n) ≠ (nb076_alpha_dummy_038 m n) from (by
          unfold
            nb076_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0031
                    m n)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_032) ≠ (nb076_alpha_dummy_039) from (by
          unfold
            nb076_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0028)
                  0)))) (show (nb076_alpha_dummy_035 m n) ≠ (nb076_alpha_dummy_040 m n) from (by
          unfold
            nb076_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0029
                    m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_032) ≠ (nb076_alpha_dummy_037)
        from (by
          unfold
            nb076_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0026)
                  0)))) (show (nb076_alpha_dummy_035 m n) ≠ (nb076_alpha_dummy_038 m n) from (by
          unfold
            nb076_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0027
                    m n)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_033) ≠ (nb076_alpha_dummy_039)
        from (by
          unfold
            nb076_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0032)
                  0)))) (show (nb076_alpha_dummy_036 m n) ≠ (nb076_alpha_dummy_040 m n) from (by
          unfold
            nb076_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0033
                    m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_033) ≠ (nb076_alpha_dummy_037)
        from (by
          unfold
            nb076_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0030)
                  0)))) (show (nb076_alpha_dummy_036 m n) ≠ (nb076_alpha_dummy_038 m n) from (by
          unfold
            nb076_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0031
                    m n)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb076_alpha_dummy_033), (nb076_alpha_dummy_036 m n)), ((nb076_alpha_dummy_032),
        (nb076_alpha_dummy_035 m n)), ((nb076_alpha_dummy_031), (nb076_alpha_dummy_034 m n)),
        ((nb076_alpha_dummy_029), (nb076_alpha_dummy_030 m n)), ((nb076_alpha_dummy_025),
        (nb076_alpha_dummy_027 m n)), ((nb076_alpha_dummy_026), (nb076_alpha_dummy_028 m n)),
        ((nb076_alpha_dummy_018), (nb076_alpha_dummy_020 m n)), ((nb076_alpha_dummy_017),
        (nb076_alpha_dummy_019 m n)), ((nb076_alpha_dummy_023), (nb076_alpha_dummy_024 m n)),
        ((nb076_alpha_dummy_021), (nb076_alpha_dummy_022 m n)), ((nb076_alpha_dummy_010),
        (nb076_alpha_dummy_012 g m n a b)), ((nb076_alpha_dummy_009),
        (nb076_alpha_dummy_011 g m n a b)), ((nb076_alpha_dummy_015),
        (nb076_alpha_dummy_016 g m n a b)), ((nb076_alpha_dummy_013),
        (nb076_alpha_dummy_014 g m n a b)), ((nb076_alpha_dummy_005),
        (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n),
        ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007),
        (nb076_alpha_dummy_008 g m n a b))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_025))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_027 m
        n))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_032) ≠ (nb076_alpha_dummy_043) from (by
          unfold
            nb076_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0036)
                  0)))) (show (nb076_alpha_dummy_035 m n) ≠ (nb076_alpha_dummy_044 m n) from (by
          unfold
            nb076_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0037
                    m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_032) ≠ (nb076_alpha_dummy_041)
        from (by
          unfold
            nb076_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0034)
                  0)))) (show (nb076_alpha_dummy_035 m n) ≠ (nb076_alpha_dummy_042 m n) from (by
          unfold
            nb076_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0035
                    m n)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_032) ≠ (nb076_alpha_dummy_043)
        from (by
          unfold
            nb076_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0036)
                  0)))) (show (nb076_alpha_dummy_035 m n) ≠ (nb076_alpha_dummy_044 m n) from (by
          unfold
            nb076_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0037
                    m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_032) ≠ (nb076_alpha_dummy_041)
        from (by
          unfold
            nb076_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0034)
                  0)))) (show (nb076_alpha_dummy_035 m n) ≠ (nb076_alpha_dummy_042 m n) from (by
          unfold
            nb076_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0035
                    m n)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_033) ≠ (nb076_alpha_dummy_045) from (by
          unfold
            nb076_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0040)
                  0)))) (show (nb076_alpha_dummy_036 m n) ≠ (nb076_alpha_dummy_046 m n) from (by
          unfold
            nb076_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0041
                    m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_033) ≠ (nb076_alpha_dummy_041)
        from (by
          unfold
            nb076_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0038)
                  0)))) (show (nb076_alpha_dummy_036 m n) ≠ (nb076_alpha_dummy_042 m n) from (by
          unfold
            nb076_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0039
                    m n)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_033) ≠
        (nb076_alpha_dummy_045) from (by
          unfold
            nb076_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0040)
                  0)))) (show (nb076_alpha_dummy_036 m n) ≠ (nb076_alpha_dummy_046 m n) from (by
          unfold
            nb076_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0041
                    m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_033) ≠ (nb076_alpha_dummy_041)
        from (by
          unfold
            nb076_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0038)
                  0)))) (show (nb076_alpha_dummy_036 m n) ≠ (nb076_alpha_dummy_042 m n) from (by
          unfold
            nb076_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0039
                    m n)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb076_alpha_dummy_025) ≠ (nb076_alpha_dummy_029) from
                                        (by
                                          unfold nb076_alpha_dummy_029;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb076_support_mem_0022)
                                                  0)))) (show (nb076_alpha_dummy_027 m n) ≠
        (nb076_alpha_dummy_030 m n) from (by
                                          unfold nb076_alpha_dummy_030;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb076_support_mem_0023 m n) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb076_alpha_dummy_029), (nb076_alpha_dummy_030 m n)),
                                      ((nb076_alpha_dummy_025), (nb076_alpha_dummy_027 m n)),
                                      ((nb076_alpha_dummy_026), (nb076_alpha_dummy_028 m n)),
                                      ((nb076_alpha_dummy_018), (nb076_alpha_dummy_020 m n)),
                                      ((nb076_alpha_dummy_017), (nb076_alpha_dummy_019 m n)),
                                      ((nb076_alpha_dummy_023), (nb076_alpha_dummy_024 m n)),
                                      ((nb076_alpha_dummy_021), (nb076_alpha_dummy_022 m n)),
                                      ((nb076_alpha_dummy_010),
                                        (nb076_alpha_dummy_012 g m n a b)),
                                      ((nb076_alpha_dummy_009),
                                        (nb076_alpha_dummy_011 g m n a b)),
                                      ((nb076_alpha_dummy_015),
                                        (nb076_alpha_dummy_016 g m n a b)),
                                      ((nb076_alpha_dummy_013),
                                        (nb076_alpha_dummy_014 g m n a b)),
                                      ((nb076_alpha_dummy_005),
                                        (nb076_alpha_dummy_006 g m n a b)),
                                      ((nb076_alpha_dummy_004), n),
                                      ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007),
                                        (nb076_alpha_dummy_008 g m n a b))]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb076_alpha_dummy_025) ≠ (nb076_alpha_dummy_029) from (by
                                        unfold nb076_alpha_dummy_029;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0022)
                                                0)))) (show (nb076_alpha_dummy_027 m n) ≠
                                        (nb076_alpha_dummy_030 m n) from (by
                                        unfold nb076_alpha_dummy_030;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0023 m n) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb076_alpha_dummy_025) ≠ (nb076_alpha_dummy_029) from
                                        (by
                                          unfold nb076_alpha_dummy_029;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb076_support_mem_0022)
                                                  0)))) (show (nb076_alpha_dummy_027 m n) ≠
        (nb076_alpha_dummy_030 m n) from (by
                                          unfold nb076_alpha_dummy_030;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb076_support_mem_0023 m n) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb076_alpha_dummy_029), (nb076_alpha_dummy_030 m n)),
                                      ((nb076_alpha_dummy_025), (nb076_alpha_dummy_027 m n)),
                                      ((nb076_alpha_dummy_026), (nb076_alpha_dummy_028 m n)),
                                      ((nb076_alpha_dummy_018), (nb076_alpha_dummy_020 m n)),
                                      ((nb076_alpha_dummy_017), (nb076_alpha_dummy_019 m n)),
                                      ((nb076_alpha_dummy_023), (nb076_alpha_dummy_024 m n)),
                                      ((nb076_alpha_dummy_021), (nb076_alpha_dummy_022 m n)),
                                      ((nb076_alpha_dummy_010),
                                        (nb076_alpha_dummy_012 g m n a b)),
                                      ((nb076_alpha_dummy_009),
                                        (nb076_alpha_dummy_011 g m n a b)),
                                      ((nb076_alpha_dummy_015),
                                        (nb076_alpha_dummy_016 g m n a b)),
                                      ((nb076_alpha_dummy_013),
                                        (nb076_alpha_dummy_014 g m n a b)),
                                      ((nb076_alpha_dummy_005),
                                        (nb076_alpha_dummy_006 g m n a b)),
                                      ((nb076_alpha_dummy_004), n),
                                      ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007),
                                        (nb076_alpha_dummy_008 g m n a b))] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C076C001Part007`. -/


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
noncomputable def nb076_split_alpha_0001 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) :
    TAlphaWff
      [((nb076_alpha_dummy_049), (nb076_alpha_dummy_050 m n)),
        ((nb076_alpha_dummy_018), (nb076_alpha_dummy_020 m n)),
        ((nb076_alpha_dummy_017), (nb076_alpha_dummy_019 m n)),
        ((nb076_alpha_dummy_047), (nb076_alpha_dummy_048 m n)),
        ((nb076_alpha_dummy_021), (nb076_alpha_dummy_022 m n)),
        ((nb076_alpha_dummy_010), (nb076_alpha_dummy_012 g m n a b)),
        ((nb076_alpha_dummy_009), (nb076_alpha_dummy_011 g m n a b)),
        ((nb076_alpha_dummy_015), (nb076_alpha_dummy_016 g m n a b)),
        ((nb076_alpha_dummy_013), (nb076_alpha_dummy_014 g m n a b)),
        ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)),
        ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m),
        ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))]
      (Wff.imp (Wff.classMem (Class.cv (nb076_alpha_dummy_049))
          (syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_018))))) (Wff.neg
          (Wff.classMem (Class.cv (nb076_alpha_dummy_049)) (syn_ccompl (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb076_alpha_dummy_050 m n))
          (syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n))))) (Wff.neg
          (Wff.classMem (Class.cv (nb076_alpha_dummy_050 m n))
            (syn_ccompl (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb076_alpha_dummy_018) ≠ (nb076_alpha_dummy_025) from (by
                              unfold nb076_alpha_dummy_025;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0020) 0))))
                          (show (nb076_alpha_dummy_020 m n) ≠ (nb076_alpha_dummy_027 m n) from
                            (by
                              unfold nb076_alpha_dummy_027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0021 m n) 0))))
                          (TAlphaVar.there
                            (show (nb076_alpha_dummy_018) ≠ (nb076_alpha_dummy_026) from (by
                                unfold nb076_alpha_dummy_026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0020) 1)))) (show
                              (nb076_alpha_dummy_020 m n) ≠ (nb076_alpha_dummy_028 m n) from (by
                                unfold nb076_alpha_dummy_028;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0021 m n) 1))))
                            (TAlphaVar.there
                              (show (nb076_alpha_dummy_018) ≠ (nb076_alpha_dummy_051) from (by
                                  unfold nb076_alpha_dummy_051;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb076_support_mem_0058) 0)))) (show
                                (nb076_alpha_dummy_020 m n) ≠ (nb076_alpha_dummy_052 m n) from
                                (by
                                  unfold nb076_alpha_dummy_052;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb076_support_mem_0059 m n)
                                          0)))) (TAlphaVar.there
                                (show (nb076_alpha_dummy_018) ≠ (nb076_alpha_dummy_049) from (by
                                    unfold nb076_alpha_dummy_049;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb076_support_mem_0056) 0)))) (show
                                  (nb076_alpha_dummy_020 m n) ≠ (nb076_alpha_dummy_050 m n) from
                                  (by
                                    unfold nb076_alpha_dummy_050;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb076_support_mem_0057 m n)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb076_alpha_dummy_018))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv (nb076_alpha_dummy_020 m n))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_025) ≠ (nb076_alpha_dummy_032) from (by
          unfold nb076_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0024) 1)))) (show (nb076_alpha_dummy_027 m n) ≠
        (nb076_alpha_dummy_035 m n) from (by
          unfold nb076_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0025 m n) 1)))) (TAlphaVar.there (show
        (nb076_alpha_dummy_025) ≠ (nb076_alpha_dummy_031) from (by
          unfold nb076_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0024) 0)))) (show (nb076_alpha_dummy_027 m n) ≠
        (nb076_alpha_dummy_034 m n) from (by
          unfold nb076_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0025 m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_025) ≠ (nb076_alpha_dummy_029)
        from (by
          unfold nb076_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0022) 0)))) (show (nb076_alpha_dummy_027 m n) ≠
        (nb076_alpha_dummy_030 m n) from (by
          unfold nb076_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0023 m n)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb076_alpha_dummy_033), (nb076_alpha_dummy_036 m n)), ((nb076_alpha_dummy_032),
        (nb076_alpha_dummy_035 m n)), ((nb076_alpha_dummy_031), (nb076_alpha_dummy_034 m n)),
        ((nb076_alpha_dummy_029), (nb076_alpha_dummy_030 m n)), ((nb076_alpha_dummy_025),
        (nb076_alpha_dummy_027 m n)), ((nb076_alpha_dummy_026), (nb076_alpha_dummy_028 m n)),
        ((nb076_alpha_dummy_051), (nb076_alpha_dummy_052 m n)), ((nb076_alpha_dummy_049),
        (nb076_alpha_dummy_050 m n)), ((nb076_alpha_dummy_018), (nb076_alpha_dummy_020 m n)),
        ((nb076_alpha_dummy_017), (nb076_alpha_dummy_019 m n)), ((nb076_alpha_dummy_047),
        (nb076_alpha_dummy_048 m n)), ((nb076_alpha_dummy_021), (nb076_alpha_dummy_022 m n)),
        ((nb076_alpha_dummy_010), (nb076_alpha_dummy_012 g m n a b)), ((nb076_alpha_dummy_009),
        (nb076_alpha_dummy_011 g m n a b)), ((nb076_alpha_dummy_015),
        (nb076_alpha_dummy_016 g m n a b)), ((nb076_alpha_dummy_013),
        (nb076_alpha_dummy_014 g m n a b)), ((nb076_alpha_dummy_005),
        (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n),
        ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007),
        (nb076_alpha_dummy_008 g m n a b))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_032) ≠
        (nb076_alpha_dummy_039) from (by
          unfold
            nb076_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0028)
                  0)))) (show (nb076_alpha_dummy_035 m n) ≠ (nb076_alpha_dummy_040 m n) from (by
          unfold
            nb076_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0029
                    m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_032) ≠ (nb076_alpha_dummy_037)
        from (by
          unfold
            nb076_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0026)
                  0)))) (show (nb076_alpha_dummy_035 m n) ≠ (nb076_alpha_dummy_038 m n) from (by
          unfold
            nb076_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0027
                    m n)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_033) ≠ (nb076_alpha_dummy_039)
        from (by
          unfold
            nb076_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0032)
                  0)))) (show (nb076_alpha_dummy_036 m n) ≠ (nb076_alpha_dummy_040 m n) from (by
          unfold
            nb076_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0033
                    m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_033) ≠ (nb076_alpha_dummy_037)
        from (by
          unfold
            nb076_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0030)
                  0)))) (show (nb076_alpha_dummy_036 m n) ≠ (nb076_alpha_dummy_038 m n) from (by
          unfold
            nb076_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0031
                    m n)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_032) ≠ (nb076_alpha_dummy_039) from (by
          unfold
            nb076_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0028)
                  0)))) (show (nb076_alpha_dummy_035 m n) ≠ (nb076_alpha_dummy_040 m n) from (by
          unfold
            nb076_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0029
                    m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_032) ≠ (nb076_alpha_dummy_037)
        from (by
          unfold
            nb076_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0026)
                  0)))) (show (nb076_alpha_dummy_035 m n) ≠ (nb076_alpha_dummy_038 m n) from (by
          unfold
            nb076_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0027
                    m n)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_033) ≠ (nb076_alpha_dummy_039)
        from (by
          unfold
            nb076_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0032)
                  0)))) (show (nb076_alpha_dummy_036 m n) ≠ (nb076_alpha_dummy_040 m n) from (by
          unfold
            nb076_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0033
                    m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_033) ≠ (nb076_alpha_dummy_037)
        from (by
          unfold
            nb076_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0030)
                  0)))) (show (nb076_alpha_dummy_036 m n) ≠ (nb076_alpha_dummy_038 m n) from (by
          unfold
            nb076_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0031
                    m n)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb076_alpha_dummy_033), (nb076_alpha_dummy_036 m n)), ((nb076_alpha_dummy_032),
        (nb076_alpha_dummy_035 m n)), ((nb076_alpha_dummy_031), (nb076_alpha_dummy_034 m n)),
        ((nb076_alpha_dummy_029), (nb076_alpha_dummy_030 m n)), ((nb076_alpha_dummy_025),
        (nb076_alpha_dummy_027 m n)), ((nb076_alpha_dummy_026), (nb076_alpha_dummy_028 m n)),
        ((nb076_alpha_dummy_051), (nb076_alpha_dummy_052 m n)), ((nb076_alpha_dummy_049),
        (nb076_alpha_dummy_050 m n)), ((nb076_alpha_dummy_018), (nb076_alpha_dummy_020 m n)),
        ((nb076_alpha_dummy_017), (nb076_alpha_dummy_019 m n)), ((nb076_alpha_dummy_047),
        (nb076_alpha_dummy_048 m n)), ((nb076_alpha_dummy_021), (nb076_alpha_dummy_022 m n)),
        ((nb076_alpha_dummy_010), (nb076_alpha_dummy_012 g m n a b)), ((nb076_alpha_dummy_009),
        (nb076_alpha_dummy_011 g m n a b)), ((nb076_alpha_dummy_015),
        (nb076_alpha_dummy_016 g m n a b)), ((nb076_alpha_dummy_013),
        (nb076_alpha_dummy_014 g m n a b)), ((nb076_alpha_dummy_005),
        (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n),
        ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007),
        (nb076_alpha_dummy_008 g m n a b))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_025))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_027 m
        n))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_032) ≠ (nb076_alpha_dummy_043) from (by
          unfold
            nb076_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0036)
                  0)))) (show (nb076_alpha_dummy_035 m n) ≠ (nb076_alpha_dummy_044 m n) from (by
          unfold
            nb076_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0037
                    m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_032) ≠ (nb076_alpha_dummy_041)
        from (by
          unfold
            nb076_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0034)
                  0)))) (show (nb076_alpha_dummy_035 m n) ≠ (nb076_alpha_dummy_042 m n) from (by
          unfold
            nb076_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0035
                    m n)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_032) ≠ (nb076_alpha_dummy_043)
        from (by
          unfold
            nb076_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0036)
                  0)))) (show (nb076_alpha_dummy_035 m n) ≠ (nb076_alpha_dummy_044 m n) from (by
          unfold
            nb076_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0037
                    m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_032) ≠ (nb076_alpha_dummy_041)
        from (by
          unfold
            nb076_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0034)
                  0)))) (show (nb076_alpha_dummy_035 m n) ≠ (nb076_alpha_dummy_042 m n) from (by
          unfold
            nb076_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0035
                    m n)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_033) ≠ (nb076_alpha_dummy_045) from (by
          unfold
            nb076_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0040)
                  0)))) (show (nb076_alpha_dummy_036 m n) ≠ (nb076_alpha_dummy_046 m n) from (by
          unfold
            nb076_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0041
                    m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_033) ≠ (nb076_alpha_dummy_041)
        from (by
          unfold
            nb076_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0038)
                  0)))) (show (nb076_alpha_dummy_036 m n) ≠ (nb076_alpha_dummy_042 m n) from (by
          unfold
            nb076_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0039
                    m n)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_033) ≠
        (nb076_alpha_dummy_045) from (by
          unfold
            nb076_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0040)
                  0)))) (show (nb076_alpha_dummy_036 m n) ≠ (nb076_alpha_dummy_046 m n) from (by
          unfold
            nb076_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0041
                    m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_033) ≠ (nb076_alpha_dummy_041)
        from (by
          unfold
            nb076_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0038)
                  0)))) (show (nb076_alpha_dummy_036 m n) ≠ (nb076_alpha_dummy_042 m n) from (by
          unfold
            nb076_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0039
                    m n)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb076_alpha_dummy_025) ≠ (nb076_alpha_dummy_029) from (by
                                        unfold nb076_alpha_dummy_029;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0022)
                                                0)))) (show (nb076_alpha_dummy_027 m n) ≠
                                        (nb076_alpha_dummy_030 m n) from (by
                                        unfold nb076_alpha_dummy_030;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0023 m n) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb076_alpha_dummy_029), (nb076_alpha_dummy_030 m n)),
                                    ((nb076_alpha_dummy_025), (nb076_alpha_dummy_027 m n)),
                                    ((nb076_alpha_dummy_026), (nb076_alpha_dummy_028 m n)),
                                    ((nb076_alpha_dummy_051), (nb076_alpha_dummy_052 m n)),
                                    ((nb076_alpha_dummy_049), (nb076_alpha_dummy_050 m n)),
                                    ((nb076_alpha_dummy_018), (nb076_alpha_dummy_020 m n)),
                                    ((nb076_alpha_dummy_017), (nb076_alpha_dummy_019 m n)),
                                    ((nb076_alpha_dummy_047), (nb076_alpha_dummy_048 m n)),
                                    ((nb076_alpha_dummy_021), (nb076_alpha_dummy_022 m n)),
                                    ((nb076_alpha_dummy_010),
                                      (nb076_alpha_dummy_012 g m n a b)),
                                    ((nb076_alpha_dummy_009),
                                      (nb076_alpha_dummy_011 g m n a b)),
                                    ((nb076_alpha_dummy_015),
                                      (nb076_alpha_dummy_016 g m n a b)),
                                    ((nb076_alpha_dummy_013),
                                      (nb076_alpha_dummy_014 g m n a b)),
                                    ((nb076_alpha_dummy_005),
                                      (nb076_alpha_dummy_006 g m n a b)),
                                    ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m),
                                    ((nb076_alpha_dummy_007),
                                      (nb076_alpha_dummy_008 g m n a b))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb076_alpha_dummy_025) ≠ (nb076_alpha_dummy_029) from
                                    (by
                                      unfold nb076_alpha_dummy_029;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb076_support_mem_0022)
                                              0)))) (show (nb076_alpha_dummy_027 m n) ≠
                                      (nb076_alpha_dummy_030 m n) from (by
                                      unfold nb076_alpha_dummy_030;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb076_support_mem_0023 m n)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb076_alpha_dummy_025) ≠ (nb076_alpha_dummy_029) from (by
                                        unfold nb076_alpha_dummy_029;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0022)
                                                0)))) (show (nb076_alpha_dummy_027 m n) ≠
                                        (nb076_alpha_dummy_030 m n) from (by
                                        unfold nb076_alpha_dummy_030;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0023 m n) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb076_alpha_dummy_029), (nb076_alpha_dummy_030 m n)),
                                    ((nb076_alpha_dummy_025), (nb076_alpha_dummy_027 m n)),
                                    ((nb076_alpha_dummy_026), (nb076_alpha_dummy_028 m n)),
                                    ((nb076_alpha_dummy_051), (nb076_alpha_dummy_052 m n)),
                                    ((nb076_alpha_dummy_049), (nb076_alpha_dummy_050 m n)),
                                    ((nb076_alpha_dummy_018), (nb076_alpha_dummy_020 m n)),
                                    ((nb076_alpha_dummy_017), (nb076_alpha_dummy_019 m n)),
                                    ((nb076_alpha_dummy_047), (nb076_alpha_dummy_048 m n)),
                                    ((nb076_alpha_dummy_021), (nb076_alpha_dummy_022 m n)),
                                    ((nb076_alpha_dummy_010),
                                      (nb076_alpha_dummy_012 g m n a b)),
                                    ((nb076_alpha_dummy_009),
                                      (nb076_alpha_dummy_011 g m n a b)),
                                    ((nb076_alpha_dummy_015),
                                      (nb076_alpha_dummy_016 g m n a b)),
                                    ((nb076_alpha_dummy_013),
                                      (nb076_alpha_dummy_014 g m n a b)),
                                    ((nb076_alpha_dummy_005),
                                      (nb076_alpha_dummy_006 g m n a b)),
                                    ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m),
                                    ((nb076_alpha_dummy_007),
                                      (nb076_alpha_dummy_008 g m n a b))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb076_alpha_dummy_018) ≠ (nb076_alpha_dummy_025) from (by
                              unfold nb076_alpha_dummy_025;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0020) 0))))
                          (show (nb076_alpha_dummy_020 m n) ≠ (nb076_alpha_dummy_027 m n) from
                            (by
                              unfold nb076_alpha_dummy_027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0021 m n) 0))))
                          (TAlphaVar.there
                            (show (nb076_alpha_dummy_018) ≠ (nb076_alpha_dummy_026) from (by
                                unfold nb076_alpha_dummy_026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0020) 1)))) (show
                              (nb076_alpha_dummy_020 m n) ≠ (nb076_alpha_dummy_028 m n) from (by
                                unfold nb076_alpha_dummy_028;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0021 m n) 1))))
                            (TAlphaVar.there
                              (show (nb076_alpha_dummy_018) ≠ (nb076_alpha_dummy_051) from (by
                                  unfold nb076_alpha_dummy_051;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb076_support_mem_0058) 0)))) (show
                                (nb076_alpha_dummy_020 m n) ≠ (nb076_alpha_dummy_052 m n) from
                                (by
                                  unfold nb076_alpha_dummy_052;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb076_support_mem_0059 m n)
                                          0)))) (TAlphaVar.there
                                (show (nb076_alpha_dummy_018) ≠ (nb076_alpha_dummy_049) from (by
                                    unfold nb076_alpha_dummy_049;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb076_support_mem_0056) 0)))) (show
                                  (nb076_alpha_dummy_020 m n) ≠ (nb076_alpha_dummy_050 m n) from
                                  (by
                                    unfold nb076_alpha_dummy_050;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb076_support_mem_0057 m n)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb076_alpha_dummy_018))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv (nb076_alpha_dummy_020 m n))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_025) ≠ (nb076_alpha_dummy_032) from (by
          unfold nb076_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0024) 1)))) (show (nb076_alpha_dummy_027 m n) ≠
        (nb076_alpha_dummy_035 m n) from (by
          unfold nb076_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0025 m n) 1)))) (TAlphaVar.there (show
        (nb076_alpha_dummy_025) ≠ (nb076_alpha_dummy_031) from (by
          unfold nb076_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0024) 0)))) (show (nb076_alpha_dummy_027 m n) ≠
        (nb076_alpha_dummy_034 m n) from (by
          unfold nb076_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0025 m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_025) ≠ (nb076_alpha_dummy_029)
        from (by
          unfold nb076_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0022) 0)))) (show (nb076_alpha_dummy_027 m n) ≠
        (nb076_alpha_dummy_030 m n) from (by
          unfold nb076_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0023 m n)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb076_alpha_dummy_033), (nb076_alpha_dummy_036 m n)), ((nb076_alpha_dummy_032),
        (nb076_alpha_dummy_035 m n)), ((nb076_alpha_dummy_031), (nb076_alpha_dummy_034 m n)),
        ((nb076_alpha_dummy_029), (nb076_alpha_dummy_030 m n)), ((nb076_alpha_dummy_025),
        (nb076_alpha_dummy_027 m n)), ((nb076_alpha_dummy_026), (nb076_alpha_dummy_028 m n)),
        ((nb076_alpha_dummy_051), (nb076_alpha_dummy_052 m n)), ((nb076_alpha_dummy_049),
        (nb076_alpha_dummy_050 m n)), ((nb076_alpha_dummy_018), (nb076_alpha_dummy_020 m n)),
        ((nb076_alpha_dummy_017), (nb076_alpha_dummy_019 m n)), ((nb076_alpha_dummy_047),
        (nb076_alpha_dummy_048 m n)), ((nb076_alpha_dummy_021), (nb076_alpha_dummy_022 m n)),
        ((nb076_alpha_dummy_010), (nb076_alpha_dummy_012 g m n a b)), ((nb076_alpha_dummy_009),
        (nb076_alpha_dummy_011 g m n a b)), ((nb076_alpha_dummy_015),
        (nb076_alpha_dummy_016 g m n a b)), ((nb076_alpha_dummy_013),
        (nb076_alpha_dummy_014 g m n a b)), ((nb076_alpha_dummy_005),
        (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n),
        ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007),
        (nb076_alpha_dummy_008 g m n a b))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_032) ≠
        (nb076_alpha_dummy_039) from (by
          unfold
            nb076_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0028)
                  0)))) (show (nb076_alpha_dummy_035 m n) ≠ (nb076_alpha_dummy_040 m n) from (by
          unfold
            nb076_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0029
                    m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_032) ≠ (nb076_alpha_dummy_037)
        from (by
          unfold
            nb076_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0026)
                  0)))) (show (nb076_alpha_dummy_035 m n) ≠ (nb076_alpha_dummy_038 m n) from (by
          unfold
            nb076_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0027
                    m n)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_033) ≠ (nb076_alpha_dummy_039)
        from (by
          unfold
            nb076_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0032)
                  0)))) (show (nb076_alpha_dummy_036 m n) ≠ (nb076_alpha_dummy_040 m n) from (by
          unfold
            nb076_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0033
                    m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_033) ≠ (nb076_alpha_dummy_037)
        from (by
          unfold
            nb076_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0030)
                  0)))) (show (nb076_alpha_dummy_036 m n) ≠ (nb076_alpha_dummy_038 m n) from (by
          unfold
            nb076_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0031
                    m n)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_032) ≠ (nb076_alpha_dummy_039) from (by
          unfold
            nb076_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0028)
                  0)))) (show (nb076_alpha_dummy_035 m n) ≠ (nb076_alpha_dummy_040 m n) from (by
          unfold
            nb076_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0029
                    m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_032) ≠ (nb076_alpha_dummy_037)
        from (by
          unfold
            nb076_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0026)
                  0)))) (show (nb076_alpha_dummy_035 m n) ≠ (nb076_alpha_dummy_038 m n) from (by
          unfold
            nb076_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0027
                    m n)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_033) ≠ (nb076_alpha_dummy_039)
        from (by
          unfold
            nb076_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0032)
                  0)))) (show (nb076_alpha_dummy_036 m n) ≠ (nb076_alpha_dummy_040 m n) from (by
          unfold
            nb076_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0033
                    m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_033) ≠ (nb076_alpha_dummy_037)
        from (by
          unfold
            nb076_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0030)
                  0)))) (show (nb076_alpha_dummy_036 m n) ≠ (nb076_alpha_dummy_038 m n) from (by
          unfold
            nb076_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0031
                    m n)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb076_alpha_dummy_033), (nb076_alpha_dummy_036 m n)), ((nb076_alpha_dummy_032),
        (nb076_alpha_dummy_035 m n)), ((nb076_alpha_dummy_031), (nb076_alpha_dummy_034 m n)),
        ((nb076_alpha_dummy_029), (nb076_alpha_dummy_030 m n)), ((nb076_alpha_dummy_025),
        (nb076_alpha_dummy_027 m n)), ((nb076_alpha_dummy_026), (nb076_alpha_dummy_028 m n)),
        ((nb076_alpha_dummy_051), (nb076_alpha_dummy_052 m n)), ((nb076_alpha_dummy_049),
        (nb076_alpha_dummy_050 m n)), ((nb076_alpha_dummy_018), (nb076_alpha_dummy_020 m n)),
        ((nb076_alpha_dummy_017), (nb076_alpha_dummy_019 m n)), ((nb076_alpha_dummy_047),
        (nb076_alpha_dummy_048 m n)), ((nb076_alpha_dummy_021), (nb076_alpha_dummy_022 m n)),
        ((nb076_alpha_dummy_010), (nb076_alpha_dummy_012 g m n a b)), ((nb076_alpha_dummy_009),
        (nb076_alpha_dummy_011 g m n a b)), ((nb076_alpha_dummy_015),
        (nb076_alpha_dummy_016 g m n a b)), ((nb076_alpha_dummy_013),
        (nb076_alpha_dummy_014 g m n a b)), ((nb076_alpha_dummy_005),
        (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n),
        ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007),
        (nb076_alpha_dummy_008 g m n a b))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_025))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_027 m
        n))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_032) ≠ (nb076_alpha_dummy_043) from (by
          unfold
            nb076_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0036)
                  0)))) (show (nb076_alpha_dummy_035 m n) ≠ (nb076_alpha_dummy_044 m n) from (by
          unfold
            nb076_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0037
                    m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_032) ≠ (nb076_alpha_dummy_041)
        from (by
          unfold
            nb076_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0034)
                  0)))) (show (nb076_alpha_dummy_035 m n) ≠ (nb076_alpha_dummy_042 m n) from (by
          unfold
            nb076_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0035
                    m n)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_032) ≠ (nb076_alpha_dummy_043)
        from (by
          unfold
            nb076_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0036)
                  0)))) (show (nb076_alpha_dummy_035 m n) ≠ (nb076_alpha_dummy_044 m n) from (by
          unfold
            nb076_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0037
                    m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_032) ≠ (nb076_alpha_dummy_041)
        from (by
          unfold
            nb076_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0034)
                  0)))) (show (nb076_alpha_dummy_035 m n) ≠ (nb076_alpha_dummy_042 m n) from (by
          unfold
            nb076_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0035
                    m n)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_033) ≠ (nb076_alpha_dummy_045) from (by
          unfold
            nb076_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0040)
                  0)))) (show (nb076_alpha_dummy_036 m n) ≠ (nb076_alpha_dummy_046 m n) from (by
          unfold
            nb076_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0041
                    m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_033) ≠ (nb076_alpha_dummy_041)
        from (by
          unfold
            nb076_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0038)
                  0)))) (show (nb076_alpha_dummy_036 m n) ≠ (nb076_alpha_dummy_042 m n) from (by
          unfold
            nb076_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0039
                    m n)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_033) ≠
        (nb076_alpha_dummy_045) from (by
          unfold
            nb076_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0040)
                  0)))) (show (nb076_alpha_dummy_036 m n) ≠ (nb076_alpha_dummy_046 m n) from (by
          unfold
            nb076_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0041
                    m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_033) ≠ (nb076_alpha_dummy_041)
        from (by
          unfold
            nb076_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0038)
                  0)))) (show (nb076_alpha_dummy_036 m n) ≠ (nb076_alpha_dummy_042 m n) from (by
          unfold
            nb076_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0039
                    m n)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb076_alpha_dummy_025) ≠ (nb076_alpha_dummy_029) from (by
                                        unfold nb076_alpha_dummy_029;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0022)
                                                0)))) (show (nb076_alpha_dummy_027 m n) ≠
                                        (nb076_alpha_dummy_030 m n) from (by
                                        unfold nb076_alpha_dummy_030;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0023 m n) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb076_alpha_dummy_029), (nb076_alpha_dummy_030 m n)),
                                    ((nb076_alpha_dummy_025), (nb076_alpha_dummy_027 m n)),
                                    ((nb076_alpha_dummy_026), (nb076_alpha_dummy_028 m n)),
                                    ((nb076_alpha_dummy_051), (nb076_alpha_dummy_052 m n)),
                                    ((nb076_alpha_dummy_049), (nb076_alpha_dummy_050 m n)),
                                    ((nb076_alpha_dummy_018), (nb076_alpha_dummy_020 m n)),
                                    ((nb076_alpha_dummy_017), (nb076_alpha_dummy_019 m n)),
                                    ((nb076_alpha_dummy_047), (nb076_alpha_dummy_048 m n)),
                                    ((nb076_alpha_dummy_021), (nb076_alpha_dummy_022 m n)),
                                    ((nb076_alpha_dummy_010),
                                      (nb076_alpha_dummy_012 g m n a b)),
                                    ((nb076_alpha_dummy_009),
                                      (nb076_alpha_dummy_011 g m n a b)),
                                    ((nb076_alpha_dummy_015),
                                      (nb076_alpha_dummy_016 g m n a b)),
                                    ((nb076_alpha_dummy_013),
                                      (nb076_alpha_dummy_014 g m n a b)),
                                    ((nb076_alpha_dummy_005),
                                      (nb076_alpha_dummy_006 g m n a b)),
                                    ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m),
                                    ((nb076_alpha_dummy_007),
                                      (nb076_alpha_dummy_008 g m n a b))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb076_alpha_dummy_025) ≠ (nb076_alpha_dummy_029) from
                                    (by
                                      unfold nb076_alpha_dummy_029;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb076_support_mem_0022)
                                              0)))) (show (nb076_alpha_dummy_027 m n) ≠
                                      (nb076_alpha_dummy_030 m n) from (by
                                      unfold nb076_alpha_dummy_030;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb076_support_mem_0023 m n)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb076_alpha_dummy_025) ≠ (nb076_alpha_dummy_029) from (by
                                        unfold nb076_alpha_dummy_029;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0022)
                                                0)))) (show (nb076_alpha_dummy_027 m n) ≠
                                        (nb076_alpha_dummy_030 m n) from (by
                                        unfold nb076_alpha_dummy_030;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0023 m n) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb076_alpha_dummy_029), (nb076_alpha_dummy_030 m n)),
                                    ((nb076_alpha_dummy_025), (nb076_alpha_dummy_027 m n)),
                                    ((nb076_alpha_dummy_026), (nb076_alpha_dummy_028 m n)),
                                    ((nb076_alpha_dummy_051), (nb076_alpha_dummy_052 m n)),
                                    ((nb076_alpha_dummy_049), (nb076_alpha_dummy_050 m n)),
                                    ((nb076_alpha_dummy_018), (nb076_alpha_dummy_020 m n)),
                                    ((nb076_alpha_dummy_017), (nb076_alpha_dummy_019 m n)),
                                    ((nb076_alpha_dummy_047), (nb076_alpha_dummy_048 m n)),
                                    ((nb076_alpha_dummy_021), (nb076_alpha_dummy_022 m n)),
                                    ((nb076_alpha_dummy_010),
                                      (nb076_alpha_dummy_012 g m n a b)),
                                    ((nb076_alpha_dummy_009),
                                      (nb076_alpha_dummy_011 g m n a b)),
                                    ((nb076_alpha_dummy_015),
                                      (nb076_alpha_dummy_016 g m n a b)),
                                    ((nb076_alpha_dummy_013),
                                      (nb076_alpha_dummy_014 g m n a b)),
                                    ((nb076_alpha_dummy_005),
                                      (nb076_alpha_dummy_006 g m n a b)),
                                    ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m),
                                    ((nb076_alpha_dummy_007),
                                      (nb076_alpha_dummy_008 g m n a b))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.refl_of_closed [((nb076_alpha_dummy_049), (nb076_alpha_dummy_050 m n)),
            ((nb076_alpha_dummy_018), (nb076_alpha_dummy_020 m n)),
            ((nb076_alpha_dummy_017), (nb076_alpha_dummy_019 m n)),
            ((nb076_alpha_dummy_047), (nb076_alpha_dummy_048 m n)),
            ((nb076_alpha_dummy_021), (nb076_alpha_dummy_022 m n)),
            ((nb076_alpha_dummy_010), (nb076_alpha_dummy_012 g m n a b)),
            ((nb076_alpha_dummy_009), (nb076_alpha_dummy_011 g m n a b)),
            ((nb076_alpha_dummy_015), (nb076_alpha_dummy_016 g m n a b)),
            ((nb076_alpha_dummy_013), (nb076_alpha_dummy_014 g m n a b)),
            ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)),
            ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m),
            ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))]
          (syn_ccompl (syn_csn (syn_c0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
