/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4C068C001Part013Stage1

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C068C001Part013`. -/


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
noncomputable def nb068_split_alpha_0000 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_021), (nb068_alpha_dummy_024 x y)),
        ((nb068_alpha_dummy_020), (nb068_alpha_dummy_023 x y)),
        ((nb068_alpha_dummy_019), (nb068_alpha_dummy_022 x y)),
        ((nb068_alpha_dummy_017), (nb068_alpha_dummy_018 x y)),
        ((nb068_alpha_dummy_013), (nb068_alpha_dummy_015 x y)),
        ((nb068_alpha_dummy_014), (nb068_alpha_dummy_016 x y)),
        ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)),
        ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)),
        ((nb068_alpha_dummy_011), (nb068_alpha_dummy_012 x y)),
        ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)),
        ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb068_alpha_dummy_020)) (Class.cv (nb068_alpha_dummy_021)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_019))
            (syn_cun (Class.cv (nb068_alpha_dummy_020)) (Class.cv (nb068_alpha_dummy_021))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_023 x y))
            (Class.cv (nb068_alpha_dummy_024 x y))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_022 x y))
            (syn_cun (Class.cv (nb068_alpha_dummy_023 x y))
              (Class.cv (nb068_alpha_dummy_024 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_020) ≠ (nb068_alpha_dummy_027) from (by
                              unfold nb068_alpha_dummy_027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0018) 0))))
                          (show (nb068_alpha_dummy_023 x y) ≠ (nb068_alpha_dummy_028 x y) from
                            (by
                              unfold nb068_alpha_dummy_028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0019 x y) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_020) ≠ (nb068_alpha_dummy_025) from (by
                                unfold nb068_alpha_dummy_025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0016) 0)))) (show
                              (nb068_alpha_dummy_023 x y) ≠ (nb068_alpha_dummy_026 x y) from (by
                                unfold nb068_alpha_dummy_026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0017 x y) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_021) ≠ (nb068_alpha_dummy_027) from (by
                              unfold nb068_alpha_dummy_027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0022) 0))))
                          (show (nb068_alpha_dummy_024 x y) ≠ (nb068_alpha_dummy_028 x y) from
                            (by
                              unfold nb068_alpha_dummy_028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0023 x y) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_021) ≠ (nb068_alpha_dummy_025) from (by
                                unfold nb068_alpha_dummy_025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0020) 0)))) (show
                              (nb068_alpha_dummy_024 x y) ≠ (nb068_alpha_dummy_026 x y) from (by
                                unfold nb068_alpha_dummy_026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0021 x y) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_020) ≠ (nb068_alpha_dummy_027) from (by
                              unfold nb068_alpha_dummy_027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0018) 0))))
                          (show (nb068_alpha_dummy_023 x y) ≠ (nb068_alpha_dummy_028 x y) from
                            (by
                              unfold nb068_alpha_dummy_028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0019 x y) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_020) ≠ (nb068_alpha_dummy_025) from (by
                                unfold nb068_alpha_dummy_025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0016) 0)))) (show
                              (nb068_alpha_dummy_023 x y) ≠ (nb068_alpha_dummy_026 x y) from (by
                                unfold nb068_alpha_dummy_026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0017 x y) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_021) ≠ (nb068_alpha_dummy_027) from (by
                              unfold nb068_alpha_dummy_027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0022) 0))))
                          (show (nb068_alpha_dummy_024 x y) ≠ (nb068_alpha_dummy_028 x y) from
                            (by
                              unfold nb068_alpha_dummy_028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0023 x y) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_021) ≠ (nb068_alpha_dummy_025) from (by
                                unfold nb068_alpha_dummy_025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0020) 0)))) (show
                              (nb068_alpha_dummy_024 x y) ≠ (nb068_alpha_dummy_026 x y) from (by
                                unfold nb068_alpha_dummy_026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0021 x y) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb068_alpha_dummy_021), (nb068_alpha_dummy_024 x y)),
          ((nb068_alpha_dummy_020), (nb068_alpha_dummy_023 x y)),
          ((nb068_alpha_dummy_019), (nb068_alpha_dummy_022 x y)),
          ((nb068_alpha_dummy_017), (nb068_alpha_dummy_018 x y)),
          ((nb068_alpha_dummy_013), (nb068_alpha_dummy_015 x y)),
          ((nb068_alpha_dummy_014), (nb068_alpha_dummy_016 x y)),
          ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)),
          ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)),
          ((nb068_alpha_dummy_011), (nb068_alpha_dummy_012 x y)),
          ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)),
          ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x),
          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_020) ≠ (nb068_alpha_dummy_031) from (by
                                unfold nb068_alpha_dummy_031;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0026) 0)))) (show
                              (nb068_alpha_dummy_023 x y) ≠ (nb068_alpha_dummy_032 x y) from (by
                                unfold nb068_alpha_dummy_032;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0027 x y) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_020) ≠ (nb068_alpha_dummy_029) from (by
                                  unfold nb068_alpha_dummy_029;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0024) 0)))) (show
                                (nb068_alpha_dummy_023 x y) ≠ (nb068_alpha_dummy_030 x y) from
                                (by
                                  unfold nb068_alpha_dummy_030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0025 x y)
                                          0)))) (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_020) ≠ (nb068_alpha_dummy_031) from (by
                                unfold nb068_alpha_dummy_031;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0026) 0)))) (show
                              (nb068_alpha_dummy_023 x y) ≠ (nb068_alpha_dummy_032 x y) from (by
                                unfold nb068_alpha_dummy_032;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0027 x y) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_020) ≠ (nb068_alpha_dummy_029) from (by
                                  unfold nb068_alpha_dummy_029;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0024) 0)))) (show
                                (nb068_alpha_dummy_023 x y) ≠ (nb068_alpha_dummy_030 x y) from
                                (by
                                  unfold nb068_alpha_dummy_030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0025 x y)
                                          0)))) (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_021) ≠ (nb068_alpha_dummy_033) from (by
                                unfold nb068_alpha_dummy_033;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0030) 0)))) (show
                              (nb068_alpha_dummy_024 x y) ≠ (nb068_alpha_dummy_034 x y) from (by
                                unfold nb068_alpha_dummy_034;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0031 x y) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_021) ≠ (nb068_alpha_dummy_029) from (by
                                  unfold nb068_alpha_dummy_029;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0028) 0)))) (show
                                (nb068_alpha_dummy_024 x y) ≠ (nb068_alpha_dummy_030 x y) from
                                (by
                                  unfold nb068_alpha_dummy_030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0029 x y)
                                          0)))) (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_021) ≠ (nb068_alpha_dummy_033) from (by
                                unfold nb068_alpha_dummy_033;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0030) 0)))) (show
                              (nb068_alpha_dummy_024 x y) ≠ (nb068_alpha_dummy_034 x y) from (by
                                unfold nb068_alpha_dummy_034;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0031 x y) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_021) ≠ (nb068_alpha_dummy_029) from (by
                                  unfold nb068_alpha_dummy_029;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0028) 0)))) (show
                                (nb068_alpha_dummy_024 x y) ≠ (nb068_alpha_dummy_030 x y) from
                                (by
                                  unfold nb068_alpha_dummy_030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0029 x y)
                                          0)))) (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part014`. -/


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
noncomputable def nb068_split_alpha_0001 (x : Var) (y : Var) (f : Var) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)),
        ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)),
        ((nb068_alpha_dummy_011), (nb068_alpha_dummy_012 x y)),
        ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)),
        ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_006))
          (Class.cv (nb068_alpha_dummy_001))) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_005))
            (syn_cphi (Class.cv (nb068_alpha_dummy_006))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_008 x y)) (Class.cv x)) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_007 x y))
            (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068_alpha_dummy_001) ≠ (nb068_alpha_dummy_006) from (by
              unfold nb068_alpha_dummy_006;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0004) 1))))
          (show x ≠ (nb068_alpha_dummy_008 x y) from (by
              unfold nb068_alpha_dummy_008;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0006 x y) 1))))
          (TAlphaVar.there (show (nb068_alpha_dummy_001) ≠ (nb068_alpha_dummy_005) from (by
                unfold nb068_alpha_dummy_005;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0004) 0))))
            (show x ≠ (nb068_alpha_dummy_007 x y) from (by
                unfold nb068_alpha_dummy_007;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0006 x y) 0))))
            (TAlphaVar.there (show (nb068_alpha_dummy_001) ≠ (nb068_alpha_dummy_011) from (by
                  unfold nb068_alpha_dummy_011;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0008) 0))))
              (show x ≠ (nb068_alpha_dummy_012 x y) from (by
                  unfold nb068_alpha_dummy_012;
                  with_reducible
                    exact
                      (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0009 x y) 0))))
              (TAlphaVar.there (show (nb068_alpha_dummy_001) ≠ (nb068_alpha_dummy_009) from (by
                    unfold nb068_alpha_dummy_009;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0005) 0))))
                (show x ≠ (nb068_alpha_dummy_010 x y) from (by
                    unfold nb068_alpha_dummy_010;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0007 x y) 0))))
                (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                  dv_x_y (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb068_alpha_dummy_001))).fv ∪
                ((Class.cv (nb068_alpha_dummy_002))).fv) (by decide))
            (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068_alpha_dummy_006) ≠ (nb068_alpha_dummy_013) from
                      (by
                        unfold nb068_alpha_dummy_013;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0010) 0))))
                    (show (nb068_alpha_dummy_008 x y) ≠ (nb068_alpha_dummy_015 x y) from (by
                        unfold nb068_alpha_dummy_015;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0011 x y) 0))))
                    (TAlphaVar.there
                      (show (nb068_alpha_dummy_006) ≠ (nb068_alpha_dummy_014) from (by
                          unfold nb068_alpha_dummy_014;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0010) 1))))
                      (show (nb068_alpha_dummy_008 x y) ≠ (nb068_alpha_dummy_016 x y) from (by
                          unfold nb068_alpha_dummy_016;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0011 x y) 1))))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_006))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb068_alpha_dummy_008 x y))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb068_alpha_dummy_013) ≠ (nb068_alpha_dummy_020) from
                                        (by
                                          unfold nb068_alpha_dummy_020;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0014)
                                                  1)))) (show (nb068_alpha_dummy_015 x y) ≠
        (nb068_alpha_dummy_023 x y) from (by
                                          unfold nb068_alpha_dummy_023;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0015 x y) 1))))
                                      (TAlphaVar.there (show (nb068_alpha_dummy_013) ≠
        (nb068_alpha_dummy_019) from (by
          unfold nb068_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0014) 0)))) (show (nb068_alpha_dummy_015 x y) ≠
        (nb068_alpha_dummy_022 x y) from (by
          unfold nb068_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0015 x y) 0)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_013) ≠ (nb068_alpha_dummy_017) from (by
          unfold nb068_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0012) 0)))) (show (nb068_alpha_dummy_015 x y) ≠
        (nb068_alpha_dummy_018 x y) from (by
          unfold nb068_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0013 x y) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb068_alpha_dummy_021),
        (nb068_alpha_dummy_024 x y)), ((nb068_alpha_dummy_020), (nb068_alpha_dummy_023 x y)),
        ((nb068_alpha_dummy_019), (nb068_alpha_dummy_022 x y)), ((nb068_alpha_dummy_017),
        (nb068_alpha_dummy_018 x y)), ((nb068_alpha_dummy_013), (nb068_alpha_dummy_015 x y)),
        ((nb068_alpha_dummy_014), (nb068_alpha_dummy_016 x y)), ((nb068_alpha_dummy_006),
        (nb068_alpha_dummy_008 x y)), ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)),
        ((nb068_alpha_dummy_011), (nb068_alpha_dummy_012 x y)), ((nb068_alpha_dummy_009),
        (nb068_alpha_dummy_010 x y)), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                                        (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb068_split_alpha_0000 x y f))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068_alpha_dummy_013) ≠ (nb068_alpha_dummy_017) from (by
                                  unfold nb068_alpha_dummy_017;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0012) 0)))) (show
                                (nb068_alpha_dummy_015 x y) ≠ (nb068_alpha_dummy_018 x y) from
                                (by
                                  unfold nb068_alpha_dummy_018;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0013 x y)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.refl_of_closed
                            [((nb068_alpha_dummy_017), (nb068_alpha_dummy_018 x y)),
                              ((nb068_alpha_dummy_013), (nb068_alpha_dummy_015 x y)),
                              ((nb068_alpha_dummy_014), (nb068_alpha_dummy_016 x y)),
                              ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)),
                              ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)),
                              ((nb068_alpha_dummy_011), (nb068_alpha_dummy_012 x y)),
                              ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)),
                              ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x),
                              ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_013) ≠ (nb068_alpha_dummy_017) from (by
                                unfold nb068_alpha_dummy_017;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0012) 0)))) (show
                              (nb068_alpha_dummy_015 x y) ≠ (nb068_alpha_dummy_018 x y) from (by
                                unfold nb068_alpha_dummy_018;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0013 x y) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068_alpha_dummy_013) ≠ (nb068_alpha_dummy_017) from (by
                                  unfold nb068_alpha_dummy_017;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0012) 0)))) (show
                                (nb068_alpha_dummy_015 x y) ≠ (nb068_alpha_dummy_018 x y) from
                                (by
                                  unfold nb068_alpha_dummy_018;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0013 x y)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.refl_of_closed
                            [((nb068_alpha_dummy_017), (nb068_alpha_dummy_018 x y)),
                              ((nb068_alpha_dummy_013), (nb068_alpha_dummy_015 x y)),
                              ((nb068_alpha_dummy_014), (nb068_alpha_dummy_016 x y)),
                              ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)),
                              ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)),
                              ((nb068_alpha_dummy_011), (nb068_alpha_dummy_012 x y)),
                              ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)),
                              ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x),
                              ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def nb068_split_alpha_0002 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_021), (nb068_alpha_dummy_024 x y)),
        ((nb068_alpha_dummy_020), (nb068_alpha_dummy_023 x y)),
        ((nb068_alpha_dummy_019), (nb068_alpha_dummy_022 x y)),
        ((nb068_alpha_dummy_017), (nb068_alpha_dummy_018 x y)),
        ((nb068_alpha_dummy_013), (nb068_alpha_dummy_015 x y)),
        ((nb068_alpha_dummy_014), (nb068_alpha_dummy_016 x y)),
        ((nb068_alpha_dummy_039), (nb068_alpha_dummy_040 x y)),
        ((nb068_alpha_dummy_037), (nb068_alpha_dummy_038 x y)),
        ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)),
        ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)),
        ((nb068_alpha_dummy_035), (nb068_alpha_dummy_036 x y)),
        ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)),
        ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb068_alpha_dummy_020)) (Class.cv (nb068_alpha_dummy_021)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_019))
            (syn_cun (Class.cv (nb068_alpha_dummy_020)) (Class.cv (nb068_alpha_dummy_021))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_023 x y))
            (Class.cv (nb068_alpha_dummy_024 x y))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_022 x y))
            (syn_cun (Class.cv (nb068_alpha_dummy_023 x y))
              (Class.cv (nb068_alpha_dummy_024 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_020) ≠ (nb068_alpha_dummy_027) from (by
                              unfold nb068_alpha_dummy_027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0018) 0))))
                          (show (nb068_alpha_dummy_023 x y) ≠ (nb068_alpha_dummy_028 x y) from
                            (by
                              unfold nb068_alpha_dummy_028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0019 x y) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_020) ≠ (nb068_alpha_dummy_025) from (by
                                unfold nb068_alpha_dummy_025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0016) 0)))) (show
                              (nb068_alpha_dummy_023 x y) ≠ (nb068_alpha_dummy_026 x y) from (by
                                unfold nb068_alpha_dummy_026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0017 x y) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_021) ≠ (nb068_alpha_dummy_027) from (by
                              unfold nb068_alpha_dummy_027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0022) 0))))
                          (show (nb068_alpha_dummy_024 x y) ≠ (nb068_alpha_dummy_028 x y) from
                            (by
                              unfold nb068_alpha_dummy_028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0023 x y) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_021) ≠ (nb068_alpha_dummy_025) from (by
                                unfold nb068_alpha_dummy_025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0020) 0)))) (show
                              (nb068_alpha_dummy_024 x y) ≠ (nb068_alpha_dummy_026 x y) from (by
                                unfold nb068_alpha_dummy_026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0021 x y) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_020) ≠ (nb068_alpha_dummy_027) from (by
                              unfold nb068_alpha_dummy_027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0018) 0))))
                          (show (nb068_alpha_dummy_023 x y) ≠ (nb068_alpha_dummy_028 x y) from
                            (by
                              unfold nb068_alpha_dummy_028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0019 x y) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_020) ≠ (nb068_alpha_dummy_025) from (by
                                unfold nb068_alpha_dummy_025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0016) 0)))) (show
                              (nb068_alpha_dummy_023 x y) ≠ (nb068_alpha_dummy_026 x y) from (by
                                unfold nb068_alpha_dummy_026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0017 x y) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_021) ≠ (nb068_alpha_dummy_027) from (by
                              unfold nb068_alpha_dummy_027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0022) 0))))
                          (show (nb068_alpha_dummy_024 x y) ≠ (nb068_alpha_dummy_028 x y) from
                            (by
                              unfold nb068_alpha_dummy_028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0023 x y) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_021) ≠ (nb068_alpha_dummy_025) from (by
                                unfold nb068_alpha_dummy_025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0020) 0)))) (show
                              (nb068_alpha_dummy_024 x y) ≠ (nb068_alpha_dummy_026 x y) from (by
                                unfold nb068_alpha_dummy_026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0021 x y) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb068_alpha_dummy_021), (nb068_alpha_dummy_024 x y)),
          ((nb068_alpha_dummy_020), (nb068_alpha_dummy_023 x y)),
          ((nb068_alpha_dummy_019), (nb068_alpha_dummy_022 x y)),
          ((nb068_alpha_dummy_017), (nb068_alpha_dummy_018 x y)),
          ((nb068_alpha_dummy_013), (nb068_alpha_dummy_015 x y)),
          ((nb068_alpha_dummy_014), (nb068_alpha_dummy_016 x y)),
          ((nb068_alpha_dummy_039), (nb068_alpha_dummy_040 x y)),
          ((nb068_alpha_dummy_037), (nb068_alpha_dummy_038 x y)),
          ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)),
          ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)),
          ((nb068_alpha_dummy_035), (nb068_alpha_dummy_036 x y)),
          ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)),
          ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x),
          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_020) ≠ (nb068_alpha_dummy_031) from (by
                                unfold nb068_alpha_dummy_031;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0026) 0)))) (show
                              (nb068_alpha_dummy_023 x y) ≠ (nb068_alpha_dummy_032 x y) from (by
                                unfold nb068_alpha_dummy_032;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0027 x y) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_020) ≠ (nb068_alpha_dummy_029) from (by
                                  unfold nb068_alpha_dummy_029;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0024) 0)))) (show
                                (nb068_alpha_dummy_023 x y) ≠ (nb068_alpha_dummy_030 x y) from
                                (by
                                  unfold nb068_alpha_dummy_030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0025 x y)
                                          0)))) (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_020) ≠ (nb068_alpha_dummy_031) from (by
                                unfold nb068_alpha_dummy_031;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0026) 0)))) (show
                              (nb068_alpha_dummy_023 x y) ≠ (nb068_alpha_dummy_032 x y) from (by
                                unfold nb068_alpha_dummy_032;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0027 x y) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_020) ≠ (nb068_alpha_dummy_029) from (by
                                  unfold nb068_alpha_dummy_029;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0024) 0)))) (show
                                (nb068_alpha_dummy_023 x y) ≠ (nb068_alpha_dummy_030 x y) from
                                (by
                                  unfold nb068_alpha_dummy_030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0025 x y)
                                          0)))) (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_021) ≠ (nb068_alpha_dummy_033) from (by
                                unfold nb068_alpha_dummy_033;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0030) 0)))) (show
                              (nb068_alpha_dummy_024 x y) ≠ (nb068_alpha_dummy_034 x y) from (by
                                unfold nb068_alpha_dummy_034;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0031 x y) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_021) ≠ (nb068_alpha_dummy_029) from (by
                                  unfold nb068_alpha_dummy_029;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0028) 0)))) (show
                                (nb068_alpha_dummy_024 x y) ≠ (nb068_alpha_dummy_030 x y) from
                                (by
                                  unfold nb068_alpha_dummy_030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0029 x y)
                                          0)))) (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_021) ≠ (nb068_alpha_dummy_033) from (by
                                unfold nb068_alpha_dummy_033;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0030) 0)))) (show
                              (nb068_alpha_dummy_024 x y) ≠ (nb068_alpha_dummy_034 x y) from (by
                                unfold nb068_alpha_dummy_034;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0031 x y) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_021) ≠ (nb068_alpha_dummy_029) from (by
                                  unfold nb068_alpha_dummy_029;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0028) 0)))) (show
                                (nb068_alpha_dummy_024 x y) ≠ (nb068_alpha_dummy_030 x y) from
                                (by
                                  unfold nb068_alpha_dummy_030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0029 x y)
                                          0)))) (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb068_split_alpha_0003 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_039), (nb068_alpha_dummy_040 x y)),
        ((nb068_alpha_dummy_037), (nb068_alpha_dummy_038 x y)),
        ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)),
        ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)),
        ((nb068_alpha_dummy_035), (nb068_alpha_dummy_036 x y)),
        ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)),
        ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_039))
          (syn_cphi (Class.cv (nb068_alpha_dummy_006)))) (Wff.neg
          (Wff.classMem (Class.cv (nb068_alpha_dummy_039))
            (syn_cphi (Class.cv (nb068_alpha_dummy_006))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_040 x y))
          (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))) (Wff.neg
          (Wff.classMem (Class.cv (nb068_alpha_dummy_040 x y))
            (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb068_alpha_dummy_006) ≠ (nb068_alpha_dummy_013) from
                    (by
                      unfold nb068_alpha_dummy_013;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0010) 0))))
                  (show (nb068_alpha_dummy_008 x y) ≠ (nb068_alpha_dummy_015 x y) from (by
                      unfold nb068_alpha_dummy_015;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb068_support_mem_0011 x y) 0)))) (TAlphaVar.there
                    (show (nb068_alpha_dummy_006) ≠ (nb068_alpha_dummy_014) from (by
                        unfold nb068_alpha_dummy_014;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0010) 1))))
                    (show (nb068_alpha_dummy_008 x y) ≠ (nb068_alpha_dummy_016 x y) from (by
                        unfold nb068_alpha_dummy_016;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0011 x y) 1))))
                    (TAlphaVar.there
                      (show (nb068_alpha_dummy_006) ≠ (nb068_alpha_dummy_039) from (by
                          unfold nb068_alpha_dummy_039;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0040) 0))))
                      (show (nb068_alpha_dummy_008 x y) ≠ (nb068_alpha_dummy_040 x y) from (by
                          unfold nb068_alpha_dummy_040;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0041 x y) 0))))
                      (TAlphaVar.there
                        (show (nb068_alpha_dummy_006) ≠ (nb068_alpha_dummy_037) from (by
                            unfold nb068_alpha_dummy_037;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0038) 0))))
                        (show (nb068_alpha_dummy_008 x y) ≠ (nb068_alpha_dummy_038 x y) from (by
                            unfold nb068_alpha_dummy_038;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0039 x y) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_006))).fv)
                    (by decide))
                  (freshVar_injective (((Class.cv (nb068_alpha_dummy_008 x y))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb068_alpha_dummy_013) ≠ (nb068_alpha_dummy_020) from (by
                                        unfold nb068_alpha_dummy_020;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0014)
                                                1)))) (show (nb068_alpha_dummy_015 x y) ≠
                                        (nb068_alpha_dummy_023 x y) from (by
                                        unfold nb068_alpha_dummy_023;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb068_support_mem_0015 x y) 1))))
                                    (TAlphaVar.there (show
                                        (nb068_alpha_dummy_013) ≠ (nb068_alpha_dummy_019) from
                                        (by
                                          unfold nb068_alpha_dummy_019;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0014)
                                                  0)))) (show (nb068_alpha_dummy_015 x y) ≠
        (nb068_alpha_dummy_022 x y) from (by
                                          unfold nb068_alpha_dummy_022;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0015 x y) 0))))
                                      (TAlphaVar.there (show (nb068_alpha_dummy_013) ≠
        (nb068_alpha_dummy_017) from (by
          unfold nb068_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0012) 0)))) (show (nb068_alpha_dummy_015 x y) ≠
        (nb068_alpha_dummy_018 x y) from (by
          unfold nb068_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0013 x y) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb068_alpha_dummy_021),
        (nb068_alpha_dummy_024 x y)), ((nb068_alpha_dummy_020), (nb068_alpha_dummy_023 x y)),
                                        ((nb068_alpha_dummy_019), (nb068_alpha_dummy_022 x y)),
                                        ((nb068_alpha_dummy_017), (nb068_alpha_dummy_018 x y)),
                                        ((nb068_alpha_dummy_013), (nb068_alpha_dummy_015 x y)),
                                        ((nb068_alpha_dummy_014), (nb068_alpha_dummy_016 x y)),
                                        ((nb068_alpha_dummy_039), (nb068_alpha_dummy_040 x y)),
                                        ((nb068_alpha_dummy_037), (nb068_alpha_dummy_038 x y)),
                                        ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)),
                                        ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)),
                                        ((nb068_alpha_dummy_035), (nb068_alpha_dummy_036 x y)),
                                        ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)),
                                        ((nb068_alpha_dummy_002), y),
                                        ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003),
        (nb068_alpha_dummy_004 x y f))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.neg (nb068_split_alpha_0002 x y f))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_013) ≠ (nb068_alpha_dummy_017) from (by
                                unfold nb068_alpha_dummy_017;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0012) 0)))) (show
                              (nb068_alpha_dummy_015 x y) ≠ (nb068_alpha_dummy_018 x y) from (by
                                unfold nb068_alpha_dummy_018;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0013 x y) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb068_alpha_dummy_017), (nb068_alpha_dummy_018 x y)),
                            ((nb068_alpha_dummy_013), (nb068_alpha_dummy_015 x y)),
                            ((nb068_alpha_dummy_014), (nb068_alpha_dummy_016 x y)),
                            ((nb068_alpha_dummy_039), (nb068_alpha_dummy_040 x y)),
                            ((nb068_alpha_dummy_037), (nb068_alpha_dummy_038 x y)),
                            ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)),
                            ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)),
                            ((nb068_alpha_dummy_035), (nb068_alpha_dummy_036 x y)),
                            ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)),
                            ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x),
                            ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_013) ≠ (nb068_alpha_dummy_017) from (by
                              unfold nb068_alpha_dummy_017;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0012) 0))))
                          (show (nb068_alpha_dummy_015 x y) ≠ (nb068_alpha_dummy_018 x y) from
                            (by
                              unfold nb068_alpha_dummy_018;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0013 x y) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_013) ≠ (nb068_alpha_dummy_017) from (by
                                unfold nb068_alpha_dummy_017;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0012) 0)))) (show
                              (nb068_alpha_dummy_015 x y) ≠ (nb068_alpha_dummy_018 x y) from (by
                                unfold nb068_alpha_dummy_018;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0013 x y) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb068_alpha_dummy_017), (nb068_alpha_dummy_018 x y)),
                            ((nb068_alpha_dummy_013), (nb068_alpha_dummy_015 x y)),
                            ((nb068_alpha_dummy_014), (nb068_alpha_dummy_016 x y)),
                            ((nb068_alpha_dummy_039), (nb068_alpha_dummy_040 x y)),
                            ((nb068_alpha_dummy_037), (nb068_alpha_dummy_038 x y)),
                            ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)),
                            ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)),
                            ((nb068_alpha_dummy_035), (nb068_alpha_dummy_036 x y)),
                            ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)),
                            ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x),
                            ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb068_alpha_dummy_006) ≠ (nb068_alpha_dummy_013) from (by
                        unfold nb068_alpha_dummy_013;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0010) 0))))
                    (show (nb068_alpha_dummy_008 x y) ≠ (nb068_alpha_dummy_015 x y) from (by
                        unfold nb068_alpha_dummy_015;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0011 x y) 0))))
                    (TAlphaVar.there
                      (show (nb068_alpha_dummy_006) ≠ (nb068_alpha_dummy_014) from (by
                          unfold nb068_alpha_dummy_014;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0010) 1))))
                      (show (nb068_alpha_dummy_008 x y) ≠ (nb068_alpha_dummy_016 x y) from (by
                          unfold nb068_alpha_dummy_016;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0011 x y) 1))))
                      (TAlphaVar.there
                        (show (nb068_alpha_dummy_006) ≠ (nb068_alpha_dummy_039) from (by
                            unfold nb068_alpha_dummy_039;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0040) 0))))
                        (show (nb068_alpha_dummy_008 x y) ≠ (nb068_alpha_dummy_040 x y) from (by
                            unfold nb068_alpha_dummy_040;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0041 x y) 0))))
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_006) ≠ (nb068_alpha_dummy_037) from (by
                              unfold nb068_alpha_dummy_037;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0038) 0))))
                          (show (nb068_alpha_dummy_008 x y) ≠ (nb068_alpha_dummy_038 x y) from
                            (by
                              unfold nb068_alpha_dummy_038;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0039 x y) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_006))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb068_alpha_dummy_008 x y))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb068_alpha_dummy_013) ≠ (nb068_alpha_dummy_020) from
                                        (by
                                          unfold nb068_alpha_dummy_020;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0014)
                                                  1)))) (show (nb068_alpha_dummy_015 x y) ≠
        (nb068_alpha_dummy_023 x y) from (by
                                          unfold nb068_alpha_dummy_023;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0015 x y) 1))))
                                      (TAlphaVar.there (show (nb068_alpha_dummy_013) ≠
        (nb068_alpha_dummy_019) from (by
          unfold nb068_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0014) 0)))) (show (nb068_alpha_dummy_015 x y) ≠
        (nb068_alpha_dummy_022 x y) from (by
          unfold nb068_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0015 x y) 0)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_013) ≠ (nb068_alpha_dummy_017) from (by
          unfold nb068_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0012) 0)))) (show (nb068_alpha_dummy_015 x y) ≠
        (nb068_alpha_dummy_018 x y) from (by
          unfold nb068_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0013 x y) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb068_alpha_dummy_021),
        (nb068_alpha_dummy_024 x y)), ((nb068_alpha_dummy_020), (nb068_alpha_dummy_023 x y)),
        ((nb068_alpha_dummy_019), (nb068_alpha_dummy_022 x y)), ((nb068_alpha_dummy_017),
        (nb068_alpha_dummy_018 x y)), ((nb068_alpha_dummy_013), (nb068_alpha_dummy_015 x y)),
        ((nb068_alpha_dummy_014), (nb068_alpha_dummy_016 x y)), ((nb068_alpha_dummy_039),
        (nb068_alpha_dummy_040 x y)), ((nb068_alpha_dummy_037), (nb068_alpha_dummy_038 x y)),
        ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)), ((nb068_alpha_dummy_005),
        (nb068_alpha_dummy_007 x y)), ((nb068_alpha_dummy_035), (nb068_alpha_dummy_036 x y)),
        ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                                        (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb068_split_alpha_0002 x y f))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068_alpha_dummy_013) ≠ (nb068_alpha_dummy_017) from (by
                                  unfold nb068_alpha_dummy_017;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0012) 0)))) (show
                                (nb068_alpha_dummy_015 x y) ≠ (nb068_alpha_dummy_018 x y) from
                                (by
                                  unfold nb068_alpha_dummy_018;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0013 x y)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.refl_of_closed
                            [((nb068_alpha_dummy_017), (nb068_alpha_dummy_018 x y)),
                              ((nb068_alpha_dummy_013), (nb068_alpha_dummy_015 x y)),
                              ((nb068_alpha_dummy_014), (nb068_alpha_dummy_016 x y)),
                              ((nb068_alpha_dummy_039), (nb068_alpha_dummy_040 x y)),
                              ((nb068_alpha_dummy_037), (nb068_alpha_dummy_038 x y)),
                              ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)),
                              ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)),
                              ((nb068_alpha_dummy_035), (nb068_alpha_dummy_036 x y)),
                              ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)),
                              ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x),
                              ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_013) ≠ (nb068_alpha_dummy_017) from (by
                                unfold nb068_alpha_dummy_017;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0012) 0)))) (show
                              (nb068_alpha_dummy_015 x y) ≠ (nb068_alpha_dummy_018 x y) from (by
                                unfold nb068_alpha_dummy_018;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0013 x y) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068_alpha_dummy_013) ≠ (nb068_alpha_dummy_017) from (by
                                  unfold nb068_alpha_dummy_017;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0012) 0)))) (show
                                (nb068_alpha_dummy_015 x y) ≠ (nb068_alpha_dummy_018 x y) from
                                (by
                                  unfold nb068_alpha_dummy_018;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0013 x y)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.refl_of_closed
                            [((nb068_alpha_dummy_017), (nb068_alpha_dummy_018 x y)),
                              ((nb068_alpha_dummy_013), (nb068_alpha_dummy_015 x y)),
                              ((nb068_alpha_dummy_014), (nb068_alpha_dummy_016 x y)),
                              ((nb068_alpha_dummy_039), (nb068_alpha_dummy_040 x y)),
                              ((nb068_alpha_dummy_037), (nb068_alpha_dummy_038 x y)),
                              ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)),
                              ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)),
                              ((nb068_alpha_dummy_035), (nb068_alpha_dummy_036 x y)),
                              ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)),
                              ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x),
                              ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def nb068_split_alpha_0004 (x : Var) (y : Var) (f : Var) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.classEq (Class.cv (nb068_alpha_dummy_003))
        (syn_cop (Class.cv (nb068_alpha_dummy_001)) (Class.cv (nb068_alpha_dummy_002))))
      (Wff.classEq (Class.cv (nb068_alpha_dummy_004 x y f))
        (syn_cop (Class.cv x) (Class.cv y))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
          (show (nb068_alpha_dummy_002) ≠ (nb068_alpha_dummy_003) from (by
              unfold nb068_alpha_dummy_003;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0002) 0))))) (Ne.symm
          (show y ≠ (nb068_alpha_dummy_004 x y f) from (by
              unfold nb068_alpha_dummy_004;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0003 x y f) 0)))))
        (TAlphaVar.there (Ne.symm (show (nb068_alpha_dummy_001) ≠ (nb068_alpha_dummy_003) from
              (by
                unfold nb068_alpha_dummy_003;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0000) 0))))) (Ne.symm
            (show x ≠ (nb068_alpha_dummy_004 x y f) from (by
                unfold nb068_alpha_dummy_004;
                with_reducible
                  exact
                    (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0001 x y f) 0)))))
          (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (nb068_split_alpha_0001 x y f dv_x_y)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (nb068_split_alpha_0001 x y f dv_x_y)))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb068_alpha_dummy_002) ≠ (nb068_alpha_dummy_006) from (by
                                    unfold nb068_alpha_dummy_006;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0032) 1))))
                                (show y ≠ (nb068_alpha_dummy_008 x y) from (by
                                    unfold nb068_alpha_dummy_008;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0034 x y)
                                            1)))) (TAlphaVar.there
                                  (show (nb068_alpha_dummy_002) ≠ (nb068_alpha_dummy_005) from
                                    (by
                                      unfold nb068_alpha_dummy_005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0032)
                                              0)))) (show y ≠ (nb068_alpha_dummy_007 x y) from
                                    (by
                                      unfold nb068_alpha_dummy_007;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0034 x y)
                                              0)))) (TAlphaVar.there (show
                                      (nb068_alpha_dummy_002) ≠ (nb068_alpha_dummy_035) from (by
                                        unfold nb068_alpha_dummy_035;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0036)
                                                0)))) (show y ≠ (nb068_alpha_dummy_036 x y) from
                                      (by
                                        unfold nb068_alpha_dummy_036;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb068_support_mem_0037 x y) 0))))
                                    (TAlphaVar.there (show
                                        (nb068_alpha_dummy_002) ≠ (nb068_alpha_dummy_009) from
                                        (by
                                          unfold nb068_alpha_dummy_009;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0033)
                                                  0))))
                                      (show y ≠ (nb068_alpha_dummy_010 x y) from (by
                                          unfold nb068_alpha_dummy_010;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0035 x y) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_001))).fv ∪
                                    ((Class.cv (nb068_alpha_dummy_002))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg
                                        (TAlphaWff.neg (nb068_split_alpha_0003 x y f)))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb068_alpha_dummy_037),
        (nb068_alpha_dummy_038 x y)), ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)),
                                        ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)),
                                        ((nb068_alpha_dummy_035), (nb068_alpha_dummy_036 x y)),
                                        ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)),
                                        ((nb068_alpha_dummy_002), y),
                                        ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003),
        (nb068_alpha_dummy_004 x y f))] (syn_ccompl (syn_csn (syn_c0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb068_alpha_dummy_002) ≠ (nb068_alpha_dummy_006) from (by
                                    unfold nb068_alpha_dummy_006;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0032) 1))))
                                (show y ≠ (nb068_alpha_dummy_008 x y) from (by
                                    unfold nb068_alpha_dummy_008;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0034 x y)
                                            1)))) (TAlphaVar.there
                                  (show (nb068_alpha_dummy_002) ≠ (nb068_alpha_dummy_005) from
                                    (by
                                      unfold nb068_alpha_dummy_005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0032)
                                              0)))) (show y ≠ (nb068_alpha_dummy_007 x y) from
                                    (by
                                      unfold nb068_alpha_dummy_007;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0034 x y)
                                              0)))) (TAlphaVar.there (show
                                      (nb068_alpha_dummy_002) ≠ (nb068_alpha_dummy_035) from (by
                                        unfold nb068_alpha_dummy_035;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0036)
                                                0)))) (show y ≠ (nb068_alpha_dummy_036 x y) from
                                      (by
                                        unfold nb068_alpha_dummy_036;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb068_support_mem_0037 x y) 0))))
                                    (TAlphaVar.there (show
                                        (nb068_alpha_dummy_002) ≠ (nb068_alpha_dummy_009) from
                                        (by
                                          unfold nb068_alpha_dummy_009;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0033)
                                                  0))))
                                      (show y ≠ (nb068_alpha_dummy_010 x y) from (by
                                          unfold nb068_alpha_dummy_010;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0035 x y) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_001))).fv ∪
                                    ((Class.cv (nb068_alpha_dummy_002))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg
                                        (TAlphaWff.neg (nb068_split_alpha_0003 x y f)))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb068_alpha_dummy_037),
        (nb068_alpha_dummy_038 x y)), ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)),
                                        ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)),
                                        ((nb068_alpha_dummy_035), (nb068_alpha_dummy_036 x y)),
                                        ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)),
                                        ((nb068_alpha_dummy_002), y),
                                        ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003),
        (nb068_alpha_dummy_004 x y f))] (syn_ccompl (syn_csn (syn_c0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
