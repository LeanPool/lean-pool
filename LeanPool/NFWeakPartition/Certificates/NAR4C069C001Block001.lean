/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4C069C001Part002Stage1

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C069C001Part002`. -/


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
noncomputable def nb069_split_alpha_0000 (x : Var) (y : Var) (a : Var) (b : Var) :
    TAlphaWff
      [((nb069_alpha_dummy_022), (nb069_alpha_dummy_025 a b)),
        ((nb069_alpha_dummy_021), (nb069_alpha_dummy_024 a b)),
        ((nb069_alpha_dummy_020), (nb069_alpha_dummy_023 a b)),
        ((nb069_alpha_dummy_018), (nb069_alpha_dummy_019 a b)),
        ((nb069_alpha_dummy_014), (nb069_alpha_dummy_016 a b)),
        ((nb069_alpha_dummy_015), (nb069_alpha_dummy_017 a b)),
        ((nb069_alpha_dummy_007), (nb069_alpha_dummy_009 a b)),
        ((nb069_alpha_dummy_006), (nb069_alpha_dummy_008 a b)),
        ((nb069_alpha_dummy_012), (nb069_alpha_dummy_013 a b)),
        ((nb069_alpha_dummy_010), (nb069_alpha_dummy_011 a b)),
        ((nb069_alpha_dummy_001), b), ((nb069_alpha_dummy_000), a),
        ((nb069_alpha_dummy_004), (nb069_alpha_dummy_005 x y a b))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb069_alpha_dummy_021)) (Class.cv (nb069_alpha_dummy_022)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb069_alpha_dummy_020))
            (syn_cun (Class.cv (nb069_alpha_dummy_021)) (Class.cv (nb069_alpha_dummy_022))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb069_alpha_dummy_024 a b))
            (Class.cv (nb069_alpha_dummy_025 a b))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb069_alpha_dummy_023 a b))
            (syn_cun (Class.cv (nb069_alpha_dummy_024 a b))
              (Class.cv (nb069_alpha_dummy_025 a b)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb069_alpha_dummy_021) ≠ (nb069_alpha_dummy_028) from (by
                              unfold nb069_alpha_dummy_028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb069_support_mem_0018) 0))))
                          (show (nb069_alpha_dummy_024 a b) ≠ (nb069_alpha_dummy_029 a b) from
                            (by
                              unfold nb069_alpha_dummy_029;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb069_support_mem_0019 a b) 0))))
                          (TAlphaVar.there
                            (show (nb069_alpha_dummy_021) ≠ (nb069_alpha_dummy_026) from (by
                                unfold nb069_alpha_dummy_026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0016) 0)))) (show
                              (nb069_alpha_dummy_024 a b) ≠ (nb069_alpha_dummy_027 a b) from (by
                                unfold nb069_alpha_dummy_027;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0017 a b) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb069_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb069_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb069_alpha_dummy_022) ≠ (nb069_alpha_dummy_028) from (by
                              unfold nb069_alpha_dummy_028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb069_support_mem_0022) 0))))
                          (show (nb069_alpha_dummy_025 a b) ≠ (nb069_alpha_dummy_029 a b) from
                            (by
                              unfold nb069_alpha_dummy_029;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb069_support_mem_0023 a b) 0))))
                          (TAlphaVar.there
                            (show (nb069_alpha_dummy_022) ≠ (nb069_alpha_dummy_026) from (by
                                unfold nb069_alpha_dummy_026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0020) 0)))) (show
                              (nb069_alpha_dummy_025 a b) ≠ (nb069_alpha_dummy_027 a b) from (by
                                unfold nb069_alpha_dummy_027;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0021 a b) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb069_alpha_dummy_021) ≠ (nb069_alpha_dummy_028) from (by
                              unfold nb069_alpha_dummy_028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb069_support_mem_0018) 0))))
                          (show (nb069_alpha_dummy_024 a b) ≠ (nb069_alpha_dummy_029 a b) from
                            (by
                              unfold nb069_alpha_dummy_029;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb069_support_mem_0019 a b) 0))))
                          (TAlphaVar.there
                            (show (nb069_alpha_dummy_021) ≠ (nb069_alpha_dummy_026) from (by
                                unfold nb069_alpha_dummy_026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0016) 0)))) (show
                              (nb069_alpha_dummy_024 a b) ≠ (nb069_alpha_dummy_027 a b) from (by
                                unfold nb069_alpha_dummy_027;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0017 a b) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb069_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb069_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb069_alpha_dummy_022) ≠ (nb069_alpha_dummy_028) from (by
                              unfold nb069_alpha_dummy_028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb069_support_mem_0022) 0))))
                          (show (nb069_alpha_dummy_025 a b) ≠ (nb069_alpha_dummy_029 a b) from
                            (by
                              unfold nb069_alpha_dummy_029;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb069_support_mem_0023 a b) 0))))
                          (TAlphaVar.there
                            (show (nb069_alpha_dummy_022) ≠ (nb069_alpha_dummy_026) from (by
                                unfold nb069_alpha_dummy_026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0020) 0)))) (show
                              (nb069_alpha_dummy_025 a b) ≠ (nb069_alpha_dummy_027 a b) from (by
                                unfold nb069_alpha_dummy_027;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0021 a b) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb069_alpha_dummy_022), (nb069_alpha_dummy_025 a b)),
          ((nb069_alpha_dummy_021), (nb069_alpha_dummy_024 a b)),
          ((nb069_alpha_dummy_020), (nb069_alpha_dummy_023 a b)),
          ((nb069_alpha_dummy_018), (nb069_alpha_dummy_019 a b)),
          ((nb069_alpha_dummy_014), (nb069_alpha_dummy_016 a b)),
          ((nb069_alpha_dummy_015), (nb069_alpha_dummy_017 a b)),
          ((nb069_alpha_dummy_007), (nb069_alpha_dummy_009 a b)),
          ((nb069_alpha_dummy_006), (nb069_alpha_dummy_008 a b)),
          ((nb069_alpha_dummy_012), (nb069_alpha_dummy_013 a b)),
          ((nb069_alpha_dummy_010), (nb069_alpha_dummy_011 a b)),
          ((nb069_alpha_dummy_001), b), ((nb069_alpha_dummy_000), a),
          ((nb069_alpha_dummy_004), (nb069_alpha_dummy_005 x y a b))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb069_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb069_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb069_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb069_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb069_alpha_dummy_021) ≠ (nb069_alpha_dummy_032) from (by
                                unfold nb069_alpha_dummy_032;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0026) 0)))) (show
                              (nb069_alpha_dummy_024 a b) ≠ (nb069_alpha_dummy_033 a b) from (by
                                unfold nb069_alpha_dummy_033;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0027 a b) 0))))
                            (TAlphaVar.there
                              (show (nb069_alpha_dummy_021) ≠ (nb069_alpha_dummy_030) from (by
                                  unfold nb069_alpha_dummy_030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0024) 0)))) (show
                                (nb069_alpha_dummy_024 a b) ≠ (nb069_alpha_dummy_031 a b) from
                                (by
                                  unfold nb069_alpha_dummy_031;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0025 a b)
                                          0)))) (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb069_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb069_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb069_alpha_dummy_021) ≠ (nb069_alpha_dummy_032) from (by
                                unfold nb069_alpha_dummy_032;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0026) 0)))) (show
                              (nb069_alpha_dummy_024 a b) ≠ (nb069_alpha_dummy_033 a b) from (by
                                unfold nb069_alpha_dummy_033;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0027 a b) 0))))
                            (TAlphaVar.there
                              (show (nb069_alpha_dummy_021) ≠ (nb069_alpha_dummy_030) from (by
                                  unfold nb069_alpha_dummy_030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0024) 0)))) (show
                                (nb069_alpha_dummy_024 a b) ≠ (nb069_alpha_dummy_031 a b) from
                                (by
                                  unfold nb069_alpha_dummy_031;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0025 a b)
                                          0)))) (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb069_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb069_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb069_alpha_dummy_022) ≠ (nb069_alpha_dummy_034) from (by
                                unfold nb069_alpha_dummy_034;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0030) 0)))) (show
                              (nb069_alpha_dummy_025 a b) ≠ (nb069_alpha_dummy_035 a b) from (by
                                unfold nb069_alpha_dummy_035;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0031 a b) 0))))
                            (TAlphaVar.there
                              (show (nb069_alpha_dummy_022) ≠ (nb069_alpha_dummy_030) from (by
                                  unfold nb069_alpha_dummy_030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0028) 0)))) (show
                                (nb069_alpha_dummy_025 a b) ≠ (nb069_alpha_dummy_031 a b) from
                                (by
                                  unfold nb069_alpha_dummy_031;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0029 a b)
                                          0)))) (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb069_alpha_dummy_022) ≠ (nb069_alpha_dummy_034) from (by
                                unfold nb069_alpha_dummy_034;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0030) 0)))) (show
                              (nb069_alpha_dummy_025 a b) ≠ (nb069_alpha_dummy_035 a b) from (by
                                unfold nb069_alpha_dummy_035;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0031 a b) 0))))
                            (TAlphaVar.there
                              (show (nb069_alpha_dummy_022) ≠ (nb069_alpha_dummy_030) from (by
                                  unfold nb069_alpha_dummy_030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0028) 0)))) (show
                                (nb069_alpha_dummy_025 a b) ≠ (nb069_alpha_dummy_031 a b) from
                                (by
                                  unfold nb069_alpha_dummy_031;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0029 a b)
                                          0)))) (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb069_split_alpha_0001 (x : Var) (y : Var) (a : Var) (b : Var)
    (dv_a_b : a ≠ b) :
    TAlphaWff
      [((nb069_alpha_dummy_007), (nb069_alpha_dummy_009 a b)),
        ((nb069_alpha_dummy_006), (nb069_alpha_dummy_008 a b)),
        ((nb069_alpha_dummy_012), (nb069_alpha_dummy_013 a b)),
        ((nb069_alpha_dummy_010), (nb069_alpha_dummy_011 a b)),
        ((nb069_alpha_dummy_001), b), ((nb069_alpha_dummy_000), a),
        ((nb069_alpha_dummy_004), (nb069_alpha_dummy_005 x y a b))]
      (Wff.imp (Wff.classMem (Class.cv (nb069_alpha_dummy_007))
          (Class.cv (nb069_alpha_dummy_000))) (Wff.neg
          (Wff.classEq (Class.cv (nb069_alpha_dummy_006))
            (syn_cphi (Class.cv (nb069_alpha_dummy_007))))))
      (Wff.imp (Wff.classMem (Class.cv (nb069_alpha_dummy_009 a b)) (Class.cv a)) (Wff.neg
          (Wff.classEq (Class.cv (nb069_alpha_dummy_008 a b))
            (syn_cphi (Class.cv (nb069_alpha_dummy_009 a b)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb069_alpha_dummy_000) ≠ (nb069_alpha_dummy_007) from (by
              unfold nb069_alpha_dummy_007;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0004) 1))))
          (show a ≠ (nb069_alpha_dummy_009 a b) from (by
              unfold nb069_alpha_dummy_009;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0006 a b) 1))))
          (TAlphaVar.there (show (nb069_alpha_dummy_000) ≠ (nb069_alpha_dummy_006) from (by
                unfold nb069_alpha_dummy_006;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0004) 0))))
            (show a ≠ (nb069_alpha_dummy_008 a b) from (by
                unfold nb069_alpha_dummy_008;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0006 a b) 0))))
            (TAlphaVar.there (show (nb069_alpha_dummy_000) ≠ (nb069_alpha_dummy_012) from (by
                  unfold nb069_alpha_dummy_012;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0008) 0))))
              (show a ≠ (nb069_alpha_dummy_013 a b) from (by
                  unfold nb069_alpha_dummy_013;
                  with_reducible
                    exact
                      (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0009 a b) 0))))
              (TAlphaVar.there (show (nb069_alpha_dummy_000) ≠ (nb069_alpha_dummy_010) from (by
                    unfold nb069_alpha_dummy_010;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0005) 0))))
                (show a ≠ (nb069_alpha_dummy_011 a b) from (by
                    unfold nb069_alpha_dummy_011;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0007 a b) 0))))
                (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                  dv_a_b (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb069_alpha_dummy_000))).fv ∪
                ((Class.cv (nb069_alpha_dummy_001))).fv) (by decide))
            (freshVar_injective (((Class.cv a)).fv ∪ ((Class.cv b)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb069_alpha_dummy_007) ≠ (nb069_alpha_dummy_014) from
                      (by
                        unfold nb069_alpha_dummy_014;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0010) 0))))
                    (show (nb069_alpha_dummy_009 a b) ≠ (nb069_alpha_dummy_016 a b) from (by
                        unfold nb069_alpha_dummy_016;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb069_support_mem_0011 a b) 0))))
                    (TAlphaVar.there
                      (show (nb069_alpha_dummy_007) ≠ (nb069_alpha_dummy_015) from (by
                          unfold nb069_alpha_dummy_015;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb069_support_mem_0010) 1))))
                      (show (nb069_alpha_dummy_009 a b) ≠ (nb069_alpha_dummy_017 a b) from (by
                          unfold nb069_alpha_dummy_017;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb069_support_mem_0011 a b) 1))))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb069_alpha_dummy_007))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb069_alpha_dummy_009 a b))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb069_alpha_dummy_014) ≠ (nb069_alpha_dummy_021) from
                                        (by
                                          unfold nb069_alpha_dummy_021;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb069_support_mem_0014)
                                                  1)))) (show (nb069_alpha_dummy_016 a b) ≠
        (nb069_alpha_dummy_024 a b) from (by
                                          unfold nb069_alpha_dummy_024;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb069_support_mem_0015 a b) 1))))
                                      (TAlphaVar.there (show (nb069_alpha_dummy_014) ≠
        (nb069_alpha_dummy_020) from (by
          unfold nb069_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0014) 0)))) (show (nb069_alpha_dummy_016 a b) ≠
        (nb069_alpha_dummy_023 a b) from (by
          unfold nb069_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0015 a b) 0)))) (TAlphaVar.there (show
        (nb069_alpha_dummy_014) ≠ (nb069_alpha_dummy_018) from (by
          unfold nb069_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0012) 0)))) (show (nb069_alpha_dummy_016 a b) ≠
        (nb069_alpha_dummy_019 a b) from (by
          unfold nb069_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0013 a b) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb069_alpha_dummy_022),
        (nb069_alpha_dummy_025 a b)), ((nb069_alpha_dummy_021), (nb069_alpha_dummy_024 a b)),
        ((nb069_alpha_dummy_020), (nb069_alpha_dummy_023 a b)), ((nb069_alpha_dummy_018),
        (nb069_alpha_dummy_019 a b)), ((nb069_alpha_dummy_014), (nb069_alpha_dummy_016 a b)),
        ((nb069_alpha_dummy_015), (nb069_alpha_dummy_017 a b)), ((nb069_alpha_dummy_007),
        (nb069_alpha_dummy_009 a b)), ((nb069_alpha_dummy_006), (nb069_alpha_dummy_008 a b)),
        ((nb069_alpha_dummy_012), (nb069_alpha_dummy_013 a b)), ((nb069_alpha_dummy_010),
        (nb069_alpha_dummy_011 a b)), ((nb069_alpha_dummy_001), b),
        ((nb069_alpha_dummy_000), a), ((nb069_alpha_dummy_004),
        (nb069_alpha_dummy_005 x y a b))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb069_split_alpha_0000 x y a b))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (show (nb069_alpha_dummy_014) ≠ (nb069_alpha_dummy_018) from (by
                                  unfold nb069_alpha_dummy_018;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0012) 0)))) (show
                                (nb069_alpha_dummy_016 a b) ≠ (nb069_alpha_dummy_019 a b) from
                                (by
                                  unfold nb069_alpha_dummy_019;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0013 a b)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.refl_of_closed
                            [((nb069_alpha_dummy_018), (nb069_alpha_dummy_019 a b)),
                              ((nb069_alpha_dummy_014), (nb069_alpha_dummy_016 a b)),
                              ((nb069_alpha_dummy_015), (nb069_alpha_dummy_017 a b)),
                              ((nb069_alpha_dummy_007), (nb069_alpha_dummy_009 a b)),
                              ((nb069_alpha_dummy_006), (nb069_alpha_dummy_008 a b)),
                              ((nb069_alpha_dummy_012), (nb069_alpha_dummy_013 a b)),
                              ((nb069_alpha_dummy_010), (nb069_alpha_dummy_011 a b)),
                              ((nb069_alpha_dummy_001), b), ((nb069_alpha_dummy_000), a),
                              ((nb069_alpha_dummy_004), (nb069_alpha_dummy_005 x y a b))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb069_alpha_dummy_014) ≠ (nb069_alpha_dummy_018) from (by
                                unfold nb069_alpha_dummy_018;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0012) 0)))) (show
                              (nb069_alpha_dummy_016 a b) ≠ (nb069_alpha_dummy_019 a b) from (by
                                unfold nb069_alpha_dummy_019;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0013 a b) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb069_alpha_dummy_014) ≠ (nb069_alpha_dummy_018) from (by
                                  unfold nb069_alpha_dummy_018;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0012) 0)))) (show
                                (nb069_alpha_dummy_016 a b) ≠ (nb069_alpha_dummy_019 a b) from
                                (by
                                  unfold nb069_alpha_dummy_019;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0013 a b)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.refl_of_closed
                            [((nb069_alpha_dummy_018), (nb069_alpha_dummy_019 a b)),
                              ((nb069_alpha_dummy_014), (nb069_alpha_dummy_016 a b)),
                              ((nb069_alpha_dummy_015), (nb069_alpha_dummy_017 a b)),
                              ((nb069_alpha_dummy_007), (nb069_alpha_dummy_009 a b)),
                              ((nb069_alpha_dummy_006), (nb069_alpha_dummy_008 a b)),
                              ((nb069_alpha_dummy_012), (nb069_alpha_dummy_013 a b)),
                              ((nb069_alpha_dummy_010), (nb069_alpha_dummy_011 a b)),
                              ((nb069_alpha_dummy_001), b), ((nb069_alpha_dummy_000), a),
                              ((nb069_alpha_dummy_004), (nb069_alpha_dummy_005 x y a b))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def nb069_split_alpha_0002 (x : Var) (y : Var) (a : Var) (b : Var) :
    TAlphaWff
      [((nb069_alpha_dummy_022), (nb069_alpha_dummy_025 a b)),
        ((nb069_alpha_dummy_021), (nb069_alpha_dummy_024 a b)),
        ((nb069_alpha_dummy_020), (nb069_alpha_dummy_023 a b)),
        ((nb069_alpha_dummy_018), (nb069_alpha_dummy_019 a b)),
        ((nb069_alpha_dummy_014), (nb069_alpha_dummy_016 a b)),
        ((nb069_alpha_dummy_015), (nb069_alpha_dummy_017 a b)),
        ((nb069_alpha_dummy_040), (nb069_alpha_dummy_041 a b)),
        ((nb069_alpha_dummy_038), (nb069_alpha_dummy_039 a b)),
        ((nb069_alpha_dummy_007), (nb069_alpha_dummy_009 a b)),
        ((nb069_alpha_dummy_006), (nb069_alpha_dummy_008 a b)),
        ((nb069_alpha_dummy_036), (nb069_alpha_dummy_037 a b)),
        ((nb069_alpha_dummy_010), (nb069_alpha_dummy_011 a b)),
        ((nb069_alpha_dummy_001), b), ((nb069_alpha_dummy_000), a),
        ((nb069_alpha_dummy_004), (nb069_alpha_dummy_005 x y a b))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb069_alpha_dummy_021)) (Class.cv (nb069_alpha_dummy_022)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb069_alpha_dummy_020))
            (syn_cun (Class.cv (nb069_alpha_dummy_021)) (Class.cv (nb069_alpha_dummy_022))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb069_alpha_dummy_024 a b))
            (Class.cv (nb069_alpha_dummy_025 a b))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb069_alpha_dummy_023 a b))
            (syn_cun (Class.cv (nb069_alpha_dummy_024 a b))
              (Class.cv (nb069_alpha_dummy_025 a b)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb069_alpha_dummy_021) ≠ (nb069_alpha_dummy_028) from (by
                              unfold nb069_alpha_dummy_028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb069_support_mem_0018) 0))))
                          (show (nb069_alpha_dummy_024 a b) ≠ (nb069_alpha_dummy_029 a b) from
                            (by
                              unfold nb069_alpha_dummy_029;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb069_support_mem_0019 a b) 0))))
                          (TAlphaVar.there
                            (show (nb069_alpha_dummy_021) ≠ (nb069_alpha_dummy_026) from (by
                                unfold nb069_alpha_dummy_026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0016) 0)))) (show
                              (nb069_alpha_dummy_024 a b) ≠ (nb069_alpha_dummy_027 a b) from (by
                                unfold nb069_alpha_dummy_027;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0017 a b) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb069_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb069_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb069_alpha_dummy_022) ≠ (nb069_alpha_dummy_028) from (by
                              unfold nb069_alpha_dummy_028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb069_support_mem_0022) 0))))
                          (show (nb069_alpha_dummy_025 a b) ≠ (nb069_alpha_dummy_029 a b) from
                            (by
                              unfold nb069_alpha_dummy_029;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb069_support_mem_0023 a b) 0))))
                          (TAlphaVar.there
                            (show (nb069_alpha_dummy_022) ≠ (nb069_alpha_dummy_026) from (by
                                unfold nb069_alpha_dummy_026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0020) 0)))) (show
                              (nb069_alpha_dummy_025 a b) ≠ (nb069_alpha_dummy_027 a b) from (by
                                unfold nb069_alpha_dummy_027;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0021 a b) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb069_alpha_dummy_021) ≠ (nb069_alpha_dummy_028) from (by
                              unfold nb069_alpha_dummy_028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb069_support_mem_0018) 0))))
                          (show (nb069_alpha_dummy_024 a b) ≠ (nb069_alpha_dummy_029 a b) from
                            (by
                              unfold nb069_alpha_dummy_029;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb069_support_mem_0019 a b) 0))))
                          (TAlphaVar.there
                            (show (nb069_alpha_dummy_021) ≠ (nb069_alpha_dummy_026) from (by
                                unfold nb069_alpha_dummy_026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0016) 0)))) (show
                              (nb069_alpha_dummy_024 a b) ≠ (nb069_alpha_dummy_027 a b) from (by
                                unfold nb069_alpha_dummy_027;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0017 a b) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb069_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb069_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb069_alpha_dummy_022) ≠ (nb069_alpha_dummy_028) from (by
                              unfold nb069_alpha_dummy_028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb069_support_mem_0022) 0))))
                          (show (nb069_alpha_dummy_025 a b) ≠ (nb069_alpha_dummy_029 a b) from
                            (by
                              unfold nb069_alpha_dummy_029;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb069_support_mem_0023 a b) 0))))
                          (TAlphaVar.there
                            (show (nb069_alpha_dummy_022) ≠ (nb069_alpha_dummy_026) from (by
                                unfold nb069_alpha_dummy_026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0020) 0)))) (show
                              (nb069_alpha_dummy_025 a b) ≠ (nb069_alpha_dummy_027 a b) from (by
                                unfold nb069_alpha_dummy_027;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0021 a b) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb069_alpha_dummy_022), (nb069_alpha_dummy_025 a b)),
          ((nb069_alpha_dummy_021), (nb069_alpha_dummy_024 a b)),
          ((nb069_alpha_dummy_020), (nb069_alpha_dummy_023 a b)),
          ((nb069_alpha_dummy_018), (nb069_alpha_dummy_019 a b)),
          ((nb069_alpha_dummy_014), (nb069_alpha_dummy_016 a b)),
          ((nb069_alpha_dummy_015), (nb069_alpha_dummy_017 a b)),
          ((nb069_alpha_dummy_040), (nb069_alpha_dummy_041 a b)),
          ((nb069_alpha_dummy_038), (nb069_alpha_dummy_039 a b)),
          ((nb069_alpha_dummy_007), (nb069_alpha_dummy_009 a b)),
          ((nb069_alpha_dummy_006), (nb069_alpha_dummy_008 a b)),
          ((nb069_alpha_dummy_036), (nb069_alpha_dummy_037 a b)),
          ((nb069_alpha_dummy_010), (nb069_alpha_dummy_011 a b)),
          ((nb069_alpha_dummy_001), b), ((nb069_alpha_dummy_000), a),
          ((nb069_alpha_dummy_004), (nb069_alpha_dummy_005 x y a b))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb069_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb069_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb069_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb069_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb069_alpha_dummy_021) ≠ (nb069_alpha_dummy_032) from (by
                                unfold nb069_alpha_dummy_032;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0026) 0)))) (show
                              (nb069_alpha_dummy_024 a b) ≠ (nb069_alpha_dummy_033 a b) from (by
                                unfold nb069_alpha_dummy_033;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0027 a b) 0))))
                            (TAlphaVar.there
                              (show (nb069_alpha_dummy_021) ≠ (nb069_alpha_dummy_030) from (by
                                  unfold nb069_alpha_dummy_030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0024) 0)))) (show
                                (nb069_alpha_dummy_024 a b) ≠ (nb069_alpha_dummy_031 a b) from
                                (by
                                  unfold nb069_alpha_dummy_031;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0025 a b)
                                          0)))) (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb069_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb069_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb069_alpha_dummy_021) ≠ (nb069_alpha_dummy_032) from (by
                                unfold nb069_alpha_dummy_032;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0026) 0)))) (show
                              (nb069_alpha_dummy_024 a b) ≠ (nb069_alpha_dummy_033 a b) from (by
                                unfold nb069_alpha_dummy_033;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0027 a b) 0))))
                            (TAlphaVar.there
                              (show (nb069_alpha_dummy_021) ≠ (nb069_alpha_dummy_030) from (by
                                  unfold nb069_alpha_dummy_030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0024) 0)))) (show
                                (nb069_alpha_dummy_024 a b) ≠ (nb069_alpha_dummy_031 a b) from
                                (by
                                  unfold nb069_alpha_dummy_031;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0025 a b)
                                          0)))) (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb069_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb069_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb069_alpha_dummy_022) ≠ (nb069_alpha_dummy_034) from (by
                                unfold nb069_alpha_dummy_034;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0030) 0)))) (show
                              (nb069_alpha_dummy_025 a b) ≠ (nb069_alpha_dummy_035 a b) from (by
                                unfold nb069_alpha_dummy_035;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0031 a b) 0))))
                            (TAlphaVar.there
                              (show (nb069_alpha_dummy_022) ≠ (nb069_alpha_dummy_030) from (by
                                  unfold nb069_alpha_dummy_030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0028) 0)))) (show
                                (nb069_alpha_dummy_025 a b) ≠ (nb069_alpha_dummy_031 a b) from
                                (by
                                  unfold nb069_alpha_dummy_031;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0029 a b)
                                          0)))) (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb069_alpha_dummy_022) ≠ (nb069_alpha_dummy_034) from (by
                                unfold nb069_alpha_dummy_034;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0030) 0)))) (show
                              (nb069_alpha_dummy_025 a b) ≠ (nb069_alpha_dummy_035 a b) from (by
                                unfold nb069_alpha_dummy_035;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0031 a b) 0))))
                            (TAlphaVar.there
                              (show (nb069_alpha_dummy_022) ≠ (nb069_alpha_dummy_030) from (by
                                  unfold nb069_alpha_dummy_030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0028) 0)))) (show
                                (nb069_alpha_dummy_025 a b) ≠ (nb069_alpha_dummy_031 a b) from
                                (by
                                  unfold nb069_alpha_dummy_031;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0029 a b)
                                          0)))) (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C069C001Part003`. -/


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
noncomputable def nb069_split_alpha_0003 (x : Var) (y : Var) (a : Var) (b : Var) :
    TAlphaWff
      [((nb069_alpha_dummy_040), (nb069_alpha_dummy_041 a b)),
        ((nb069_alpha_dummy_038), (nb069_alpha_dummy_039 a b)),
        ((nb069_alpha_dummy_007), (nb069_alpha_dummy_009 a b)),
        ((nb069_alpha_dummy_006), (nb069_alpha_dummy_008 a b)),
        ((nb069_alpha_dummy_036), (nb069_alpha_dummy_037 a b)),
        ((nb069_alpha_dummy_010), (nb069_alpha_dummy_011 a b)),
        ((nb069_alpha_dummy_001), b), ((nb069_alpha_dummy_000), a),
        ((nb069_alpha_dummy_004), (nb069_alpha_dummy_005 x y a b))]
      (Wff.imp (Wff.classMem (Class.cv (nb069_alpha_dummy_040))
          (syn_cphi (Class.cv (nb069_alpha_dummy_007)))) (Wff.neg
          (Wff.classMem (Class.cv (nb069_alpha_dummy_040))
            (syn_cphi (Class.cv (nb069_alpha_dummy_007))))))
      (Wff.imp (Wff.classMem (Class.cv (nb069_alpha_dummy_041 a b))
          (syn_cphi (Class.cv (nb069_alpha_dummy_009 a b)))) (Wff.neg
          (Wff.classMem (Class.cv (nb069_alpha_dummy_041 a b))
            (syn_cphi (Class.cv (nb069_alpha_dummy_009 a b)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb069_alpha_dummy_007) ≠ (nb069_alpha_dummy_014) from
                    (by
                      unfold nb069_alpha_dummy_014;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0010) 0))))
                  (show (nb069_alpha_dummy_009 a b) ≠ (nb069_alpha_dummy_016 a b) from (by
                      unfold nb069_alpha_dummy_016;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb069_support_mem_0011 a b) 0)))) (TAlphaVar.there
                    (show (nb069_alpha_dummy_007) ≠ (nb069_alpha_dummy_015) from (by
                        unfold nb069_alpha_dummy_015;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0010) 1))))
                    (show (nb069_alpha_dummy_009 a b) ≠ (nb069_alpha_dummy_017 a b) from (by
                        unfold nb069_alpha_dummy_017;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb069_support_mem_0011 a b) 1))))
                    (TAlphaVar.there
                      (show (nb069_alpha_dummy_007) ≠ (nb069_alpha_dummy_040) from (by
                          unfold nb069_alpha_dummy_040;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb069_support_mem_0040) 0))))
                      (show (nb069_alpha_dummy_009 a b) ≠ (nb069_alpha_dummy_041 a b) from (by
                          unfold nb069_alpha_dummy_041;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb069_support_mem_0041 a b) 0))))
                      (TAlphaVar.there
                        (show (nb069_alpha_dummy_007) ≠ (nb069_alpha_dummy_038) from (by
                            unfold nb069_alpha_dummy_038;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb069_support_mem_0038) 0))))
                        (show (nb069_alpha_dummy_009 a b) ≠ (nb069_alpha_dummy_039 a b) from (by
                            unfold nb069_alpha_dummy_039;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb069_support_mem_0039 a b) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb069_alpha_dummy_007))).fv)
                    (by decide))
                  (freshVar_injective (((Class.cv (nb069_alpha_dummy_009 a b))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb069_alpha_dummy_014) ≠ (nb069_alpha_dummy_021) from (by
                                        unfold nb069_alpha_dummy_021;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb069_support_mem_0014)
                                                1)))) (show (nb069_alpha_dummy_016 a b) ≠
                                        (nb069_alpha_dummy_024 a b) from (by
                                        unfold nb069_alpha_dummy_024;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb069_support_mem_0015 a b) 1))))
                                    (TAlphaVar.there (show
                                        (nb069_alpha_dummy_014) ≠ (nb069_alpha_dummy_020) from
                                        (by
                                          unfold nb069_alpha_dummy_020;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb069_support_mem_0014)
                                                  0)))) (show (nb069_alpha_dummy_016 a b) ≠
        (nb069_alpha_dummy_023 a b) from (by
                                          unfold nb069_alpha_dummy_023;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb069_support_mem_0015 a b) 0))))
                                      (TAlphaVar.there (show (nb069_alpha_dummy_014) ≠
        (nb069_alpha_dummy_018) from (by
          unfold nb069_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0012) 0)))) (show (nb069_alpha_dummy_016 a b) ≠
        (nb069_alpha_dummy_019 a b) from (by
          unfold nb069_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0013 a b) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb069_alpha_dummy_022),
        (nb069_alpha_dummy_025 a b)), ((nb069_alpha_dummy_021), (nb069_alpha_dummy_024 a b)),
                                        ((nb069_alpha_dummy_020), (nb069_alpha_dummy_023 a b)),
                                        ((nb069_alpha_dummy_018), (nb069_alpha_dummy_019 a b)),
                                        ((nb069_alpha_dummy_014), (nb069_alpha_dummy_016 a b)),
                                        ((nb069_alpha_dummy_015), (nb069_alpha_dummy_017 a b)),
                                        ((nb069_alpha_dummy_040), (nb069_alpha_dummy_041 a b)),
                                        ((nb069_alpha_dummy_038), (nb069_alpha_dummy_039 a b)),
                                        ((nb069_alpha_dummy_007), (nb069_alpha_dummy_009 a b)),
                                        ((nb069_alpha_dummy_006), (nb069_alpha_dummy_008 a b)),
                                        ((nb069_alpha_dummy_036), (nb069_alpha_dummy_037 a b)),
                                        ((nb069_alpha_dummy_010), (nb069_alpha_dummy_011 a b)),
                                        ((nb069_alpha_dummy_001), b),
                                        ((nb069_alpha_dummy_000), a), ((nb069_alpha_dummy_004),
        (nb069_alpha_dummy_005 x y a b))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.neg (nb069_split_alpha_0002 x y a b))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                            (show (nb069_alpha_dummy_014) ≠ (nb069_alpha_dummy_018) from (by
                                unfold nb069_alpha_dummy_018;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0012) 0)))) (show
                              (nb069_alpha_dummy_016 a b) ≠ (nb069_alpha_dummy_019 a b) from (by
                                unfold nb069_alpha_dummy_019;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0013 a b) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb069_alpha_dummy_018), (nb069_alpha_dummy_019 a b)),
                            ((nb069_alpha_dummy_014), (nb069_alpha_dummy_016 a b)),
                            ((nb069_alpha_dummy_015), (nb069_alpha_dummy_017 a b)),
                            ((nb069_alpha_dummy_040), (nb069_alpha_dummy_041 a b)),
                            ((nb069_alpha_dummy_038), (nb069_alpha_dummy_039 a b)),
                            ((nb069_alpha_dummy_007), (nb069_alpha_dummy_009 a b)),
                            ((nb069_alpha_dummy_006), (nb069_alpha_dummy_008 a b)),
                            ((nb069_alpha_dummy_036), (nb069_alpha_dummy_037 a b)),
                            ((nb069_alpha_dummy_010), (nb069_alpha_dummy_011 a b)),
                            ((nb069_alpha_dummy_001), b), ((nb069_alpha_dummy_000), a),
                            ((nb069_alpha_dummy_004), (nb069_alpha_dummy_005 x y a b))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb069_alpha_dummy_014) ≠ (nb069_alpha_dummy_018) from (by
                              unfold nb069_alpha_dummy_018;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb069_support_mem_0012) 0))))
                          (show (nb069_alpha_dummy_016 a b) ≠ (nb069_alpha_dummy_019 a b) from
                            (by
                              unfold nb069_alpha_dummy_019;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb069_support_mem_0013 a b) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb069_alpha_dummy_014) ≠ (nb069_alpha_dummy_018) from (by
                                unfold nb069_alpha_dummy_018;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0012) 0)))) (show
                              (nb069_alpha_dummy_016 a b) ≠ (nb069_alpha_dummy_019 a b) from (by
                                unfold nb069_alpha_dummy_019;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0013 a b) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb069_alpha_dummy_018), (nb069_alpha_dummy_019 a b)),
                            ((nb069_alpha_dummy_014), (nb069_alpha_dummy_016 a b)),
                            ((nb069_alpha_dummy_015), (nb069_alpha_dummy_017 a b)),
                            ((nb069_alpha_dummy_040), (nb069_alpha_dummy_041 a b)),
                            ((nb069_alpha_dummy_038), (nb069_alpha_dummy_039 a b)),
                            ((nb069_alpha_dummy_007), (nb069_alpha_dummy_009 a b)),
                            ((nb069_alpha_dummy_006), (nb069_alpha_dummy_008 a b)),
                            ((nb069_alpha_dummy_036), (nb069_alpha_dummy_037 a b)),
                            ((nb069_alpha_dummy_010), (nb069_alpha_dummy_011 a b)),
                            ((nb069_alpha_dummy_001), b), ((nb069_alpha_dummy_000), a),
                            ((nb069_alpha_dummy_004), (nb069_alpha_dummy_005 x y a b))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb069_alpha_dummy_007) ≠ (nb069_alpha_dummy_014) from (by
                        unfold nb069_alpha_dummy_014;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0010) 0))))
                    (show (nb069_alpha_dummy_009 a b) ≠ (nb069_alpha_dummy_016 a b) from (by
                        unfold nb069_alpha_dummy_016;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb069_support_mem_0011 a b) 0))))
                    (TAlphaVar.there
                      (show (nb069_alpha_dummy_007) ≠ (nb069_alpha_dummy_015) from (by
                          unfold nb069_alpha_dummy_015;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb069_support_mem_0010) 1))))
                      (show (nb069_alpha_dummy_009 a b) ≠ (nb069_alpha_dummy_017 a b) from (by
                          unfold nb069_alpha_dummy_017;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb069_support_mem_0011 a b) 1))))
                      (TAlphaVar.there
                        (show (nb069_alpha_dummy_007) ≠ (nb069_alpha_dummy_040) from (by
                            unfold nb069_alpha_dummy_040;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb069_support_mem_0040) 0))))
                        (show (nb069_alpha_dummy_009 a b) ≠ (nb069_alpha_dummy_041 a b) from (by
                            unfold nb069_alpha_dummy_041;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb069_support_mem_0041 a b) 0))))
                        (TAlphaVar.there
                          (show (nb069_alpha_dummy_007) ≠ (nb069_alpha_dummy_038) from (by
                              unfold nb069_alpha_dummy_038;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb069_support_mem_0038) 0))))
                          (show (nb069_alpha_dummy_009 a b) ≠ (nb069_alpha_dummy_039 a b) from
                            (by
                              unfold nb069_alpha_dummy_039;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb069_support_mem_0039 a b) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb069_alpha_dummy_007))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb069_alpha_dummy_009 a b))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb069_alpha_dummy_014) ≠ (nb069_alpha_dummy_021) from
                                        (by
                                          unfold nb069_alpha_dummy_021;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb069_support_mem_0014)
                                                  1)))) (show (nb069_alpha_dummy_016 a b) ≠
        (nb069_alpha_dummy_024 a b) from (by
                                          unfold nb069_alpha_dummy_024;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb069_support_mem_0015 a b) 1))))
                                      (TAlphaVar.there (show (nb069_alpha_dummy_014) ≠
        (nb069_alpha_dummy_020) from (by
          unfold nb069_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0014) 0)))) (show (nb069_alpha_dummy_016 a b) ≠
        (nb069_alpha_dummy_023 a b) from (by
          unfold nb069_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0015 a b) 0)))) (TAlphaVar.there (show
        (nb069_alpha_dummy_014) ≠ (nb069_alpha_dummy_018) from (by
          unfold nb069_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0012) 0)))) (show (nb069_alpha_dummy_016 a b) ≠
        (nb069_alpha_dummy_019 a b) from (by
          unfold nb069_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0013 a b) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb069_alpha_dummy_022),
        (nb069_alpha_dummy_025 a b)), ((nb069_alpha_dummy_021), (nb069_alpha_dummy_024 a b)),
        ((nb069_alpha_dummy_020), (nb069_alpha_dummy_023 a b)), ((nb069_alpha_dummy_018),
        (nb069_alpha_dummy_019 a b)), ((nb069_alpha_dummy_014), (nb069_alpha_dummy_016 a b)),
        ((nb069_alpha_dummy_015), (nb069_alpha_dummy_017 a b)), ((nb069_alpha_dummy_040),
        (nb069_alpha_dummy_041 a b)), ((nb069_alpha_dummy_038), (nb069_alpha_dummy_039 a b)),
        ((nb069_alpha_dummy_007), (nb069_alpha_dummy_009 a b)), ((nb069_alpha_dummy_006),
        (nb069_alpha_dummy_008 a b)), ((nb069_alpha_dummy_036), (nb069_alpha_dummy_037 a b)),
        ((nb069_alpha_dummy_010), (nb069_alpha_dummy_011 a b)), ((nb069_alpha_dummy_001), b),
        ((nb069_alpha_dummy_000), a), ((nb069_alpha_dummy_004),
        (nb069_alpha_dummy_005 x y a b))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb069_split_alpha_0002 x y a b))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (show (nb069_alpha_dummy_014) ≠ (nb069_alpha_dummy_018) from (by
                                  unfold nb069_alpha_dummy_018;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0012) 0)))) (show
                                (nb069_alpha_dummy_016 a b) ≠ (nb069_alpha_dummy_019 a b) from
                                (by
                                  unfold nb069_alpha_dummy_019;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0013 a b)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.refl_of_closed
                            [((nb069_alpha_dummy_018), (nb069_alpha_dummy_019 a b)),
                              ((nb069_alpha_dummy_014), (nb069_alpha_dummy_016 a b)),
                              ((nb069_alpha_dummy_015), (nb069_alpha_dummy_017 a b)),
                              ((nb069_alpha_dummy_040), (nb069_alpha_dummy_041 a b)),
                              ((nb069_alpha_dummy_038), (nb069_alpha_dummy_039 a b)),
                              ((nb069_alpha_dummy_007), (nb069_alpha_dummy_009 a b)),
                              ((nb069_alpha_dummy_006), (nb069_alpha_dummy_008 a b)),
                              ((nb069_alpha_dummy_036), (nb069_alpha_dummy_037 a b)),
                              ((nb069_alpha_dummy_010), (nb069_alpha_dummy_011 a b)),
                              ((nb069_alpha_dummy_001), b), ((nb069_alpha_dummy_000), a),
                              ((nb069_alpha_dummy_004), (nb069_alpha_dummy_005 x y a b))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb069_alpha_dummy_014) ≠ (nb069_alpha_dummy_018) from (by
                                unfold nb069_alpha_dummy_018;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0012) 0)))) (show
                              (nb069_alpha_dummy_016 a b) ≠ (nb069_alpha_dummy_019 a b) from (by
                                unfold nb069_alpha_dummy_019;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb069_support_mem_0013 a b) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb069_alpha_dummy_014) ≠ (nb069_alpha_dummy_018) from (by
                                  unfold nb069_alpha_dummy_018;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0012) 0)))) (show
                                (nb069_alpha_dummy_016 a b) ≠ (nb069_alpha_dummy_019 a b) from
                                (by
                                  unfold nb069_alpha_dummy_019;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb069_support_mem_0013 a b)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.refl_of_closed
                            [((nb069_alpha_dummy_018), (nb069_alpha_dummy_019 a b)),
                              ((nb069_alpha_dummy_014), (nb069_alpha_dummy_016 a b)),
                              ((nb069_alpha_dummy_015), (nb069_alpha_dummy_017 a b)),
                              ((nb069_alpha_dummy_040), (nb069_alpha_dummy_041 a b)),
                              ((nb069_alpha_dummy_038), (nb069_alpha_dummy_039 a b)),
                              ((nb069_alpha_dummy_007), (nb069_alpha_dummy_009 a b)),
                              ((nb069_alpha_dummy_006), (nb069_alpha_dummy_008 a b)),
                              ((nb069_alpha_dummy_036), (nb069_alpha_dummy_037 a b)),
                              ((nb069_alpha_dummy_010), (nb069_alpha_dummy_011 a b)),
                              ((nb069_alpha_dummy_001), b), ((nb069_alpha_dummy_000), a),
                              ((nb069_alpha_dummy_004), (nb069_alpha_dummy_005 x y a b))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def nb069_split_alpha_0004 (x : Var) (y : Var) (a : Var) (b : Var)
    (dv_a_b : a ≠ b) :
    TAlphaWff
      [((nb069_alpha_dummy_001), b), ((nb069_alpha_dummy_000), a),
        ((nb069_alpha_dummy_004), (nb069_alpha_dummy_005 x y a b))]
      (Wff.classEq (Class.cv (nb069_alpha_dummy_004))
        (syn_cop (Class.cv (nb069_alpha_dummy_000)) (Class.cv (nb069_alpha_dummy_001))))
      (Wff.classEq (Class.cv (nb069_alpha_dummy_005 x y a b))
        (syn_cop (Class.cv a) (Class.cv b))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
          (show (nb069_alpha_dummy_001) ≠ (nb069_alpha_dummy_004) from (by
              unfold nb069_alpha_dummy_004;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0002) 0))))) (Ne.symm
          (show b ≠ (nb069_alpha_dummy_005 x y a b) from (by
              unfold nb069_alpha_dummy_005;
              with_reducible
                exact
                  (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0003 x y a b) 0)))))
        (TAlphaVar.there (Ne.symm (show (nb069_alpha_dummy_000) ≠ (nb069_alpha_dummy_004) from
              (by
                unfold nb069_alpha_dummy_004;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0000) 0))))) (Ne.symm
            (show a ≠ (nb069_alpha_dummy_005 x y a b) from (by
                unfold nb069_alpha_dummy_005;
                with_reducible
                  exact
                    (Nat.ne_of_lt (mem_lt_freshVar (nb069_support_mem_0001 x y a b) 0)))))
          (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (nb069_split_alpha_0001 x y a b dv_a_b)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex
                        (TAlphaWff.neg (nb069_split_alpha_0001 x y a b dv_a_b)))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb069_alpha_dummy_001) ≠ (nb069_alpha_dummy_007) from (by
                                    unfold nb069_alpha_dummy_007;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb069_support_mem_0032) 1))))
                                (show b ≠ (nb069_alpha_dummy_009 a b) from (by
                                    unfold nb069_alpha_dummy_009;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb069_support_mem_0034 a b)
                                            1)))) (TAlphaVar.there
                                  (show (nb069_alpha_dummy_001) ≠ (nb069_alpha_dummy_006) from
                                    (by
                                      unfold nb069_alpha_dummy_006;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb069_support_mem_0032)
                                              0)))) (show b ≠ (nb069_alpha_dummy_008 a b) from
                                    (by
                                      unfold nb069_alpha_dummy_008;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb069_support_mem_0034 a b)
                                              0)))) (TAlphaVar.there (show
                                      (nb069_alpha_dummy_001) ≠ (nb069_alpha_dummy_036) from (by
                                        unfold nb069_alpha_dummy_036;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb069_support_mem_0036)
                                                0)))) (show b ≠ (nb069_alpha_dummy_037 a b) from
                                      (by
                                        unfold nb069_alpha_dummy_037;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb069_support_mem_0037 a b) 0))))
                                    (TAlphaVar.there (show
                                        (nb069_alpha_dummy_001) ≠ (nb069_alpha_dummy_010) from
                                        (by
                                          unfold nb069_alpha_dummy_010;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb069_support_mem_0033)
                                                  0))))
                                      (show b ≠ (nb069_alpha_dummy_011 a b) from (by
                                          unfold nb069_alpha_dummy_011;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb069_support_mem_0035 a b) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb069_alpha_dummy_000))).fv ∪
                                    ((Class.cv (nb069_alpha_dummy_001))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv a)).fv ∪ ((Class.cv b)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.neg
        (nb069_split_alpha_0003 x y a b))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb069_alpha_dummy_038),
        (nb069_alpha_dummy_039 a b)), ((nb069_alpha_dummy_007), (nb069_alpha_dummy_009 a b)),
                                        ((nb069_alpha_dummy_006), (nb069_alpha_dummy_008 a b)),
                                        ((nb069_alpha_dummy_036), (nb069_alpha_dummy_037 a b)),
                                        ((nb069_alpha_dummy_010), (nb069_alpha_dummy_011 a b)),
                                        ((nb069_alpha_dummy_001), b),
                                        ((nb069_alpha_dummy_000), a), ((nb069_alpha_dummy_004),
        (nb069_alpha_dummy_005 x y a b))] (syn_ccompl (syn_csn (syn_c0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb069_alpha_dummy_001) ≠ (nb069_alpha_dummy_007) from (by
                                    unfold nb069_alpha_dummy_007;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb069_support_mem_0032) 1))))
                                (show b ≠ (nb069_alpha_dummy_009 a b) from (by
                                    unfold nb069_alpha_dummy_009;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb069_support_mem_0034 a b)
                                            1)))) (TAlphaVar.there
                                  (show (nb069_alpha_dummy_001) ≠ (nb069_alpha_dummy_006) from
                                    (by
                                      unfold nb069_alpha_dummy_006;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb069_support_mem_0032)
                                              0)))) (show b ≠ (nb069_alpha_dummy_008 a b) from
                                    (by
                                      unfold nb069_alpha_dummy_008;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb069_support_mem_0034 a b)
                                              0)))) (TAlphaVar.there (show
                                      (nb069_alpha_dummy_001) ≠ (nb069_alpha_dummy_036) from (by
                                        unfold nb069_alpha_dummy_036;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb069_support_mem_0036)
                                                0)))) (show b ≠ (nb069_alpha_dummy_037 a b) from
                                      (by
                                        unfold nb069_alpha_dummy_037;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb069_support_mem_0037 a b) 0))))
                                    (TAlphaVar.there (show
                                        (nb069_alpha_dummy_001) ≠ (nb069_alpha_dummy_010) from
                                        (by
                                          unfold nb069_alpha_dummy_010;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb069_support_mem_0033)
                                                  0))))
                                      (show b ≠ (nb069_alpha_dummy_011 a b) from (by
                                          unfold nb069_alpha_dummy_011;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb069_support_mem_0035 a b) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb069_alpha_dummy_000))).fv ∪
                                    ((Class.cv (nb069_alpha_dummy_001))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv a)).fv ∪ ((Class.cv b)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.neg
        (nb069_split_alpha_0003 x y a b))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb069_alpha_dummy_038),
        (nb069_alpha_dummy_039 a b)), ((nb069_alpha_dummy_007), (nb069_alpha_dummy_009 a b)),
                                        ((nb069_alpha_dummy_006), (nb069_alpha_dummy_008 a b)),
                                        ((nb069_alpha_dummy_036), (nb069_alpha_dummy_037 a b)),
                                        ((nb069_alpha_dummy_010), (nb069_alpha_dummy_011 a b)),
                                        ((nb069_alpha_dummy_001), b),
                                        ((nb069_alpha_dummy_000), a), ((nb069_alpha_dummy_004),
        (nb069_alpha_dummy_005 x y a b))] (syn_ccompl (syn_csn (syn_c0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))))))))))

@[expose]
noncomputable def nominal_df_lec (x : Var) (y : Var) (a : Var) (b : Var) (dv_a_b : a ≠ b)
    (dv_a_x : a ≠ x) (__dv_a_y : a ≠ y) (dv_b_x : b ≠ x) (dv_b_y : b ≠ y)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (syn_clec) (syn_copab a b
          (syn_wrex x (.cv a) (syn_wrex y (.cv b) (syn_wss (.cv x) (.cv y)))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
            (TAlphaWff.conj (nb069_split_alpha_0004 x y a b dv_a_b) (TAlphaWff.ex
                (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.cv
                      (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                        dv_a_x (TAlphaVar.there
                          (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_a_b
                          (TAlphaVar.here _ _ _))))) (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_b_y
                            (TAlphaVar.there
                              (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_b_x
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb069_alpha_dummy_002) ≠ (nb069_alpha_dummy_044) from (by
          unfold nb069_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0044) 0)))) (show x ≠ (nb069_alpha_dummy_045 x y) from (by
          unfold nb069_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0045 x y) 0)))) (TAlphaVar.there (show
        (nb069_alpha_dummy_002) ≠ (nb069_alpha_dummy_042) from (by
          unfold nb069_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0042) 0)))) (show x ≠ (nb069_alpha_dummy_043 x y) from (by
          unfold nb069_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0043 x y)
                  0)))) (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
        dv_x_y (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb069_alpha_dummy_003) ≠ (nb069_alpha_dummy_044) from (by
          unfold nb069_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0048) 0)))) (show y ≠ (nb069_alpha_dummy_045 x y) from (by
          unfold nb069_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0049 x y) 0)))) (TAlphaVar.there (show
        (nb069_alpha_dummy_003) ≠ (nb069_alpha_dummy_042) from (by
          unfold nb069_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0046) 0)))) (show y ≠ (nb069_alpha_dummy_043 x y) from (by
          unfold nb069_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0047 x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb069_alpha_dummy_002) ≠ (nb069_alpha_dummy_044) from (by
          unfold nb069_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0044) 0)))) (show x ≠ (nb069_alpha_dummy_045 x y) from (by
          unfold nb069_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0045 x y) 0)))) (TAlphaVar.there (show
        (nb069_alpha_dummy_002) ≠ (nb069_alpha_dummy_042) from (by
          unfold nb069_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0042) 0)))) (show x ≠ (nb069_alpha_dummy_043 x y) from (by
          unfold nb069_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0043 x y)
                  0)))) (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
        dv_x_y (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb069_alpha_dummy_003) ≠ (nb069_alpha_dummy_044) from (by
          unfold nb069_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0048) 0)))) (show y ≠ (nb069_alpha_dummy_045 x y) from (by
          unfold nb069_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0049 x y) 0)))) (TAlphaVar.there (show
        (nb069_alpha_dummy_003) ≠ (nb069_alpha_dummy_042) from (by
          unfold nb069_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0046) 0)))) (show y ≠ (nb069_alpha_dummy_043 x y) from (by
          unfold nb069_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb069_support_mem_0047 x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_y
                            (TAlphaVar.here _ _ _))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
