/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4C071C001Part003Stage1

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C071C001Part003`. -/


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
noncomputable def nb071_split_alpha_0000 (x : Var) :
    TAlphaWff
      [((nb071_alpha_dummy_021), (nb071_alpha_dummy_024 x)),
        ((nb071_alpha_dummy_020), (nb071_alpha_dummy_023 x)),
        ((nb071_alpha_dummy_019), (nb071_alpha_dummy_022 x)),
        ((nb071_alpha_dummy_017), (nb071_alpha_dummy_018 x)),
        ((nb071_alpha_dummy_013), (nb071_alpha_dummy_015 x)),
        ((nb071_alpha_dummy_014), (nb071_alpha_dummy_016 x)),
        ((nb071_alpha_dummy_006), (nb071_alpha_dummy_008 x)),
        ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)),
        ((nb071_alpha_dummy_011), (nb071_alpha_dummy_012 x)),
        ((nb071_alpha_dummy_009), (nb071_alpha_dummy_010 x)),
        ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)),
        ((nb071_alpha_dummy_000), x),
        ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb071_alpha_dummy_020)) (Class.cv (nb071_alpha_dummy_021)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb071_alpha_dummy_019))
            (syn_cun (Class.cv (nb071_alpha_dummy_020)) (Class.cv (nb071_alpha_dummy_021))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb071_alpha_dummy_023 x))
            (Class.cv (nb071_alpha_dummy_024 x))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb071_alpha_dummy_022 x))
            (syn_cun (Class.cv (nb071_alpha_dummy_023 x))
              (Class.cv (nb071_alpha_dummy_024 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb071_alpha_dummy_020) ≠ (nb071_alpha_dummy_027) from (by
                              unfold nb071_alpha_dummy_027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0020) 0))))
                          (show (nb071_alpha_dummy_023 x) ≠ (nb071_alpha_dummy_028 x) from (by
                              unfold nb071_alpha_dummy_028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0021 x) 0))))
                          (TAlphaVar.there
                            (show (nb071_alpha_dummy_020) ≠ (nb071_alpha_dummy_025) from (by
                                unfold nb071_alpha_dummy_025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0018) 0))))
                            (show (nb071_alpha_dummy_023 x) ≠ (nb071_alpha_dummy_026 x) from (by
                                unfold nb071_alpha_dummy_026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0019 x) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb071_alpha_dummy_021) ≠ (nb071_alpha_dummy_027) from (by
                              unfold nb071_alpha_dummy_027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0024) 0))))
                          (show (nb071_alpha_dummy_024 x) ≠ (nb071_alpha_dummy_028 x) from (by
                              unfold nb071_alpha_dummy_028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0025 x) 0))))
                          (TAlphaVar.there
                            (show (nb071_alpha_dummy_021) ≠ (nb071_alpha_dummy_025) from (by
                                unfold nb071_alpha_dummy_025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0022) 0))))
                            (show (nb071_alpha_dummy_024 x) ≠ (nb071_alpha_dummy_026 x) from (by
                                unfold nb071_alpha_dummy_026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0023 x) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb071_alpha_dummy_020) ≠ (nb071_alpha_dummy_027) from (by
                              unfold nb071_alpha_dummy_027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0020) 0))))
                          (show (nb071_alpha_dummy_023 x) ≠ (nb071_alpha_dummy_028 x) from (by
                              unfold nb071_alpha_dummy_028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0021 x) 0))))
                          (TAlphaVar.there
                            (show (nb071_alpha_dummy_020) ≠ (nb071_alpha_dummy_025) from (by
                                unfold nb071_alpha_dummy_025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0018) 0))))
                            (show (nb071_alpha_dummy_023 x) ≠ (nb071_alpha_dummy_026 x) from (by
                                unfold nb071_alpha_dummy_026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0019 x) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb071_alpha_dummy_021) ≠ (nb071_alpha_dummy_027) from (by
                              unfold nb071_alpha_dummy_027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0024) 0))))
                          (show (nb071_alpha_dummy_024 x) ≠ (nb071_alpha_dummy_028 x) from (by
                              unfold nb071_alpha_dummy_028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0025 x) 0))))
                          (TAlphaVar.there
                            (show (nb071_alpha_dummy_021) ≠ (nb071_alpha_dummy_025) from (by
                                unfold nb071_alpha_dummy_025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0022) 0))))
                            (show (nb071_alpha_dummy_024 x) ≠ (nb071_alpha_dummy_026 x) from (by
                                unfold nb071_alpha_dummy_026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0023 x) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb071_alpha_dummy_021), (nb071_alpha_dummy_024 x)),
          ((nb071_alpha_dummy_020), (nb071_alpha_dummy_023 x)),
          ((nb071_alpha_dummy_019), (nb071_alpha_dummy_022 x)),
          ((nb071_alpha_dummy_017), (nb071_alpha_dummy_018 x)),
          ((nb071_alpha_dummy_013), (nb071_alpha_dummy_015 x)),
          ((nb071_alpha_dummy_014), (nb071_alpha_dummy_016 x)),
          ((nb071_alpha_dummy_006), (nb071_alpha_dummy_008 x)),
          ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)),
          ((nb071_alpha_dummy_011), (nb071_alpha_dummy_012 x)),
          ((nb071_alpha_dummy_009), (nb071_alpha_dummy_010 x)),
          ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x),
          ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb071_alpha_dummy_020) ≠ (nb071_alpha_dummy_031) from (by
                                unfold nb071_alpha_dummy_031;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0028) 0))))
                            (show (nb071_alpha_dummy_023 x) ≠ (nb071_alpha_dummy_032 x) from (by
                                unfold nb071_alpha_dummy_032;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0029 x) 0))))
                            (TAlphaVar.there
                              (show (nb071_alpha_dummy_020) ≠ (nb071_alpha_dummy_029) from (by
                                  unfold nb071_alpha_dummy_029;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0026) 0))))
                              (show (nb071_alpha_dummy_023 x) ≠ (nb071_alpha_dummy_030 x) from
                                (by
                                  unfold nb071_alpha_dummy_030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0027 x) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb071_alpha_dummy_020) ≠ (nb071_alpha_dummy_031) from (by
                                unfold nb071_alpha_dummy_031;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0028) 0))))
                            (show (nb071_alpha_dummy_023 x) ≠ (nb071_alpha_dummy_032 x) from (by
                                unfold nb071_alpha_dummy_032;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0029 x) 0))))
                            (TAlphaVar.there
                              (show (nb071_alpha_dummy_020) ≠ (nb071_alpha_dummy_029) from (by
                                  unfold nb071_alpha_dummy_029;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0026) 0))))
                              (show (nb071_alpha_dummy_023 x) ≠ (nb071_alpha_dummy_030 x) from
                                (by
                                  unfold nb071_alpha_dummy_030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0027 x) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb071_alpha_dummy_021) ≠ (nb071_alpha_dummy_033) from (by
                                unfold nb071_alpha_dummy_033;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0032) 0))))
                            (show (nb071_alpha_dummy_024 x) ≠ (nb071_alpha_dummy_034 x) from (by
                                unfold nb071_alpha_dummy_034;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0033 x) 0))))
                            (TAlphaVar.there
                              (show (nb071_alpha_dummy_021) ≠ (nb071_alpha_dummy_029) from (by
                                  unfold nb071_alpha_dummy_029;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0030) 0))))
                              (show (nb071_alpha_dummy_024 x) ≠ (nb071_alpha_dummy_030 x) from
                                (by
                                  unfold nb071_alpha_dummy_030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0031 x) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb071_alpha_dummy_021) ≠ (nb071_alpha_dummy_033) from (by
                                unfold nb071_alpha_dummy_033;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0032) 0))))
                            (show (nb071_alpha_dummy_024 x) ≠ (nb071_alpha_dummy_034 x) from (by
                                unfold nb071_alpha_dummy_034;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0033 x) 0))))
                            (TAlphaVar.there
                              (show (nb071_alpha_dummy_021) ≠ (nb071_alpha_dummy_029) from (by
                                  unfold nb071_alpha_dummy_029;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0030) 0))))
                              (show (nb071_alpha_dummy_024 x) ≠ (nb071_alpha_dummy_030 x) from
                                (by
                                  unfold nb071_alpha_dummy_030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0031 x) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C071C001Part004`. -/


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
noncomputable def nb071_split_alpha_0001 (x : Var) :
    TAlphaWff
      [((nb071_alpha_dummy_006), (nb071_alpha_dummy_008 x)),
        ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)),
        ((nb071_alpha_dummy_011), (nb071_alpha_dummy_012 x)),
        ((nb071_alpha_dummy_009), (nb071_alpha_dummy_010 x)),
        ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)),
        ((nb071_alpha_dummy_000), x),
        ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))]
      (Wff.imp (Wff.classMem (Class.cv (nb071_alpha_dummy_006))
          (Class.cv (nb071_alpha_dummy_000))) (Wff.neg
          (Wff.classEq (Class.cv (nb071_alpha_dummy_005))
            (syn_cphi (Class.cv (nb071_alpha_dummy_006))))))
      (Wff.imp (Wff.classMem (Class.cv (nb071_alpha_dummy_008 x)) (Class.cv x)) (Wff.neg
          (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x))
            (syn_cphi (Class.cv (nb071_alpha_dummy_008 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb071_alpha_dummy_000) ≠ (nb071_alpha_dummy_006) from (by
              unfold nb071_alpha_dummy_006;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0006) 1))))
          (show x ≠ (nb071_alpha_dummy_008 x) from (by
              unfold nb071_alpha_dummy_008;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0008 x) 1))))
          (TAlphaVar.there (show (nb071_alpha_dummy_000) ≠ (nb071_alpha_dummy_005) from (by
                unfold nb071_alpha_dummy_005;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0006) 0))))
            (show x ≠ (nb071_alpha_dummy_007 x) from (by
                unfold nb071_alpha_dummy_007;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0008 x) 0))))
            (TAlphaVar.there (show (nb071_alpha_dummy_000) ≠ (nb071_alpha_dummy_011) from (by
                  unfold nb071_alpha_dummy_011;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0010) 0))))
              (show x ≠ (nb071_alpha_dummy_012 x) from (by
                  unfold nb071_alpha_dummy_012;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0011 x) 0))))
              (TAlphaVar.there (show (nb071_alpha_dummy_000) ≠ (nb071_alpha_dummy_009) from (by
                    unfold nb071_alpha_dummy_009;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0007) 0))))
                (show x ≠ (nb071_alpha_dummy_010 x) from (by
                    unfold nb071_alpha_dummy_010;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0009 x) 0))))
                (TAlphaVar.there (show (nb071_alpha_dummy_000) ≠ (nb071_alpha_dummy_001) from
                    (by
                      unfold nb071_alpha_dummy_001;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0004) 0))))
                  (show x ≠ (nb071_alpha_dummy_002 x) from (by
                      unfold nb071_alpha_dummy_002;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0005 x) 0))))
                  (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb071_alpha_dummy_000))).fv ∪
                ((Class.cv (nb071_alpha_dummy_001))).fv) (by decide)) (freshVar_injective
              (((Class.cv x)).fv ∪ ((Class.cv (nb071_alpha_dummy_002 x))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb071_alpha_dummy_006) ≠ (nb071_alpha_dummy_013) from
                      (by
                        unfold nb071_alpha_dummy_013;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0012) 0))))
                    (show (nb071_alpha_dummy_008 x) ≠ (nb071_alpha_dummy_015 x) from (by
                        unfold nb071_alpha_dummy_015;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb071_support_mem_0013 x) 0)))) (TAlphaVar.there
                      (show (nb071_alpha_dummy_006) ≠ (nb071_alpha_dummy_014) from (by
                          unfold nb071_alpha_dummy_014;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb071_support_mem_0012) 1))))
                      (show (nb071_alpha_dummy_008 x) ≠ (nb071_alpha_dummy_016 x) from (by
                          unfold nb071_alpha_dummy_016;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb071_support_mem_0013 x) 1))))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb071_alpha_dummy_006))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb071_alpha_dummy_008 x))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb071_alpha_dummy_013) ≠ (nb071_alpha_dummy_020) from
                                        (by
                                          unfold nb071_alpha_dummy_020;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb071_support_mem_0016)
                                                  1)))) (show (nb071_alpha_dummy_015 x) ≠
        (nb071_alpha_dummy_023 x) from (by
                                          unfold nb071_alpha_dummy_023;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb071_support_mem_0017 x) 1))))
                                      (TAlphaVar.there (show (nb071_alpha_dummy_013) ≠
        (nb071_alpha_dummy_019) from (by
          unfold nb071_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0016) 0)))) (show (nb071_alpha_dummy_015 x) ≠
        (nb071_alpha_dummy_022 x) from (by
          unfold nb071_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0017 x) 0)))) (TAlphaVar.there (show
        (nb071_alpha_dummy_013) ≠ (nb071_alpha_dummy_017) from (by
          unfold nb071_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0014) 0)))) (show (nb071_alpha_dummy_015 x) ≠
        (nb071_alpha_dummy_018 x) from (by
          unfold nb071_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0015 x) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb071_alpha_dummy_021),
        (nb071_alpha_dummy_024 x)), ((nb071_alpha_dummy_020), (nb071_alpha_dummy_023 x)),
        ((nb071_alpha_dummy_019), (nb071_alpha_dummy_022 x)), ((nb071_alpha_dummy_017),
        (nb071_alpha_dummy_018 x)), ((nb071_alpha_dummy_013), (nb071_alpha_dummy_015 x)),
        ((nb071_alpha_dummy_014), (nb071_alpha_dummy_016 x)), ((nb071_alpha_dummy_006),
        (nb071_alpha_dummy_008 x)), ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)),
        ((nb071_alpha_dummy_011), (nb071_alpha_dummy_012 x)), ((nb071_alpha_dummy_009),
        (nb071_alpha_dummy_010 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)),
        ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))]
                                        (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb071_split_alpha_0000 x))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (show (nb071_alpha_dummy_013) ≠ (nb071_alpha_dummy_017) from (by
                                  unfold nb071_alpha_dummy_017;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0014) 0))))
                              (show (nb071_alpha_dummy_015 x) ≠ (nb071_alpha_dummy_018 x) from
                                (by
                                  unfold nb071_alpha_dummy_018;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0015 x) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb071_alpha_dummy_017), (nb071_alpha_dummy_018 x)),
                              ((nb071_alpha_dummy_013), (nb071_alpha_dummy_015 x)),
                              ((nb071_alpha_dummy_014), (nb071_alpha_dummy_016 x)),
                              ((nb071_alpha_dummy_006), (nb071_alpha_dummy_008 x)),
                              ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)),
                              ((nb071_alpha_dummy_011), (nb071_alpha_dummy_012 x)),
                              ((nb071_alpha_dummy_009), (nb071_alpha_dummy_010 x)),
                              ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)),
                              ((nb071_alpha_dummy_000), x),
                              ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb071_alpha_dummy_013) ≠ (nb071_alpha_dummy_017) from (by
                                unfold nb071_alpha_dummy_017;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0014) 0))))
                            (show (nb071_alpha_dummy_015 x) ≠ (nb071_alpha_dummy_018 x) from (by
                                unfold nb071_alpha_dummy_018;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0015 x) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb071_alpha_dummy_013) ≠ (nb071_alpha_dummy_017) from (by
                                  unfold nb071_alpha_dummy_017;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0014) 0))))
                              (show (nb071_alpha_dummy_015 x) ≠ (nb071_alpha_dummy_018 x) from
                                (by
                                  unfold nb071_alpha_dummy_018;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0015 x) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb071_alpha_dummy_017), (nb071_alpha_dummy_018 x)),
                              ((nb071_alpha_dummy_013), (nb071_alpha_dummy_015 x)),
                              ((nb071_alpha_dummy_014), (nb071_alpha_dummy_016 x)),
                              ((nb071_alpha_dummy_006), (nb071_alpha_dummy_008 x)),
                              ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)),
                              ((nb071_alpha_dummy_011), (nb071_alpha_dummy_012 x)),
                              ((nb071_alpha_dummy_009), (nb071_alpha_dummy_010 x)),
                              ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)),
                              ((nb071_alpha_dummy_000), x),
                              ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def nb071_split_alpha_0002 (x : Var) :
    TAlphaWff
      [((nb071_alpha_dummy_021), (nb071_alpha_dummy_024 x)),
        ((nb071_alpha_dummy_020), (nb071_alpha_dummy_023 x)),
        ((nb071_alpha_dummy_019), (nb071_alpha_dummy_022 x)),
        ((nb071_alpha_dummy_017), (nb071_alpha_dummy_018 x)),
        ((nb071_alpha_dummy_013), (nb071_alpha_dummy_015 x)),
        ((nb071_alpha_dummy_014), (nb071_alpha_dummy_016 x)),
        ((nb071_alpha_dummy_039), (nb071_alpha_dummy_040 x)),
        ((nb071_alpha_dummy_037), (nb071_alpha_dummy_038 x)),
        ((nb071_alpha_dummy_006), (nb071_alpha_dummy_008 x)),
        ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)),
        ((nb071_alpha_dummy_035), (nb071_alpha_dummy_036 x)),
        ((nb071_alpha_dummy_009), (nb071_alpha_dummy_010 x)),
        ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)),
        ((nb071_alpha_dummy_000), x),
        ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb071_alpha_dummy_020)) (Class.cv (nb071_alpha_dummy_021)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb071_alpha_dummy_019))
            (syn_cun (Class.cv (nb071_alpha_dummy_020)) (Class.cv (nb071_alpha_dummy_021))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb071_alpha_dummy_023 x))
            (Class.cv (nb071_alpha_dummy_024 x))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb071_alpha_dummy_022 x))
            (syn_cun (Class.cv (nb071_alpha_dummy_023 x))
              (Class.cv (nb071_alpha_dummy_024 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb071_alpha_dummy_020) ≠ (nb071_alpha_dummy_027) from (by
                              unfold nb071_alpha_dummy_027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0020) 0))))
                          (show (nb071_alpha_dummy_023 x) ≠ (nb071_alpha_dummy_028 x) from (by
                              unfold nb071_alpha_dummy_028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0021 x) 0))))
                          (TAlphaVar.there
                            (show (nb071_alpha_dummy_020) ≠ (nb071_alpha_dummy_025) from (by
                                unfold nb071_alpha_dummy_025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0018) 0))))
                            (show (nb071_alpha_dummy_023 x) ≠ (nb071_alpha_dummy_026 x) from (by
                                unfold nb071_alpha_dummy_026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0019 x) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb071_alpha_dummy_021) ≠ (nb071_alpha_dummy_027) from (by
                              unfold nb071_alpha_dummy_027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0024) 0))))
                          (show (nb071_alpha_dummy_024 x) ≠ (nb071_alpha_dummy_028 x) from (by
                              unfold nb071_alpha_dummy_028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0025 x) 0))))
                          (TAlphaVar.there
                            (show (nb071_alpha_dummy_021) ≠ (nb071_alpha_dummy_025) from (by
                                unfold nb071_alpha_dummy_025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0022) 0))))
                            (show (nb071_alpha_dummy_024 x) ≠ (nb071_alpha_dummy_026 x) from (by
                                unfold nb071_alpha_dummy_026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0023 x) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb071_alpha_dummy_020) ≠ (nb071_alpha_dummy_027) from (by
                              unfold nb071_alpha_dummy_027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0020) 0))))
                          (show (nb071_alpha_dummy_023 x) ≠ (nb071_alpha_dummy_028 x) from (by
                              unfold nb071_alpha_dummy_028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0021 x) 0))))
                          (TAlphaVar.there
                            (show (nb071_alpha_dummy_020) ≠ (nb071_alpha_dummy_025) from (by
                                unfold nb071_alpha_dummy_025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0018) 0))))
                            (show (nb071_alpha_dummy_023 x) ≠ (nb071_alpha_dummy_026 x) from (by
                                unfold nb071_alpha_dummy_026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0019 x) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb071_alpha_dummy_021) ≠ (nb071_alpha_dummy_027) from (by
                              unfold nb071_alpha_dummy_027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0024) 0))))
                          (show (nb071_alpha_dummy_024 x) ≠ (nb071_alpha_dummy_028 x) from (by
                              unfold nb071_alpha_dummy_028;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0025 x) 0))))
                          (TAlphaVar.there
                            (show (nb071_alpha_dummy_021) ≠ (nb071_alpha_dummy_025) from (by
                                unfold nb071_alpha_dummy_025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0022) 0))))
                            (show (nb071_alpha_dummy_024 x) ≠ (nb071_alpha_dummy_026 x) from (by
                                unfold nb071_alpha_dummy_026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0023 x) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb071_alpha_dummy_021), (nb071_alpha_dummy_024 x)),
          ((nb071_alpha_dummy_020), (nb071_alpha_dummy_023 x)),
          ((nb071_alpha_dummy_019), (nb071_alpha_dummy_022 x)),
          ((nb071_alpha_dummy_017), (nb071_alpha_dummy_018 x)),
          ((nb071_alpha_dummy_013), (nb071_alpha_dummy_015 x)),
          ((nb071_alpha_dummy_014), (nb071_alpha_dummy_016 x)),
          ((nb071_alpha_dummy_039), (nb071_alpha_dummy_040 x)),
          ((nb071_alpha_dummy_037), (nb071_alpha_dummy_038 x)),
          ((nb071_alpha_dummy_006), (nb071_alpha_dummy_008 x)),
          ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)),
          ((nb071_alpha_dummy_035), (nb071_alpha_dummy_036 x)),
          ((nb071_alpha_dummy_009), (nb071_alpha_dummy_010 x)),
          ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x),
          ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb071_alpha_dummy_020) ≠ (nb071_alpha_dummy_031) from (by
                                unfold nb071_alpha_dummy_031;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0028) 0))))
                            (show (nb071_alpha_dummy_023 x) ≠ (nb071_alpha_dummy_032 x) from (by
                                unfold nb071_alpha_dummy_032;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0029 x) 0))))
                            (TAlphaVar.there
                              (show (nb071_alpha_dummy_020) ≠ (nb071_alpha_dummy_029) from (by
                                  unfold nb071_alpha_dummy_029;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0026) 0))))
                              (show (nb071_alpha_dummy_023 x) ≠ (nb071_alpha_dummy_030 x) from
                                (by
                                  unfold nb071_alpha_dummy_030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0027 x) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb071_alpha_dummy_020) ≠ (nb071_alpha_dummy_031) from (by
                                unfold nb071_alpha_dummy_031;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0028) 0))))
                            (show (nb071_alpha_dummy_023 x) ≠ (nb071_alpha_dummy_032 x) from (by
                                unfold nb071_alpha_dummy_032;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0029 x) 0))))
                            (TAlphaVar.there
                              (show (nb071_alpha_dummy_020) ≠ (nb071_alpha_dummy_029) from (by
                                  unfold nb071_alpha_dummy_029;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0026) 0))))
                              (show (nb071_alpha_dummy_023 x) ≠ (nb071_alpha_dummy_030 x) from
                                (by
                                  unfold nb071_alpha_dummy_030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0027 x) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb071_alpha_dummy_021) ≠ (nb071_alpha_dummy_033) from (by
                                unfold nb071_alpha_dummy_033;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0032) 0))))
                            (show (nb071_alpha_dummy_024 x) ≠ (nb071_alpha_dummy_034 x) from (by
                                unfold nb071_alpha_dummy_034;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0033 x) 0))))
                            (TAlphaVar.there
                              (show (nb071_alpha_dummy_021) ≠ (nb071_alpha_dummy_029) from (by
                                  unfold nb071_alpha_dummy_029;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0030) 0))))
                              (show (nb071_alpha_dummy_024 x) ≠ (nb071_alpha_dummy_030 x) from
                                (by
                                  unfold nb071_alpha_dummy_030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0031 x) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb071_alpha_dummy_021) ≠ (nb071_alpha_dummy_033) from (by
                                unfold nb071_alpha_dummy_033;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0032) 0))))
                            (show (nb071_alpha_dummy_024 x) ≠ (nb071_alpha_dummy_034 x) from (by
                                unfold nb071_alpha_dummy_034;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0033 x) 0))))
                            (TAlphaVar.there
                              (show (nb071_alpha_dummy_021) ≠ (nb071_alpha_dummy_029) from (by
                                  unfold nb071_alpha_dummy_029;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0030) 0))))
                              (show (nb071_alpha_dummy_024 x) ≠ (nb071_alpha_dummy_030 x) from
                                (by
                                  unfold nb071_alpha_dummy_030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0031 x) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb071_split_alpha_0003 (x : Var) :
    TAlphaWff
      [((nb071_alpha_dummy_039), (nb071_alpha_dummy_040 x)),
        ((nb071_alpha_dummy_037), (nb071_alpha_dummy_038 x)),
        ((nb071_alpha_dummy_006), (nb071_alpha_dummy_008 x)),
        ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)),
        ((nb071_alpha_dummy_035), (nb071_alpha_dummy_036 x)),
        ((nb071_alpha_dummy_009), (nb071_alpha_dummy_010 x)),
        ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)),
        ((nb071_alpha_dummy_000), x),
        ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))]
      (Wff.classMem (Class.cv (nb071_alpha_dummy_039))
        (syn_cphi (Class.cv (nb071_alpha_dummy_006))))
      (Wff.classMem (Class.cv (nb071_alpha_dummy_040 x))
        (syn_cphi (Class.cv (nb071_alpha_dummy_008 x)))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cv (TAlphaVar.there
                (show (nb071_alpha_dummy_006) ≠ (nb071_alpha_dummy_013) from (by
                    unfold nb071_alpha_dummy_013;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0012) 0))))
                (show (nb071_alpha_dummy_008 x) ≠ (nb071_alpha_dummy_015 x) from (by
                    unfold nb071_alpha_dummy_015;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0013 x) 0))))
                (TAlphaVar.there (show (nb071_alpha_dummy_006) ≠ (nb071_alpha_dummy_014) from
                    (by
                      unfold nb071_alpha_dummy_014;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0012) 1))))
                  (show (nb071_alpha_dummy_008 x) ≠ (nb071_alpha_dummy_016 x) from (by
                      unfold nb071_alpha_dummy_016;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0013 x) 1))))
                  (TAlphaVar.there (show (nb071_alpha_dummy_006) ≠ (nb071_alpha_dummy_039) from
                      (by
                        unfold nb071_alpha_dummy_039;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0042) 0))))
                    (show (nb071_alpha_dummy_008 x) ≠ (nb071_alpha_dummy_040 x) from (by
                        unfold nb071_alpha_dummy_040;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb071_support_mem_0043 x) 0)))) (TAlphaVar.there
                      (show (nb071_alpha_dummy_006) ≠ (nb071_alpha_dummy_037) from (by
                          unfold nb071_alpha_dummy_037;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb071_support_mem_0040) 0))))
                      (show (nb071_alpha_dummy_008 x) ≠ (nb071_alpha_dummy_038 x) from (by
                          unfold nb071_alpha_dummy_038;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb071_support_mem_0041 x) 0))))
                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
              (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb071_alpha_dummy_006))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb071_alpha_dummy_008 x))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb071_alpha_dummy_013) ≠ (nb071_alpha_dummy_020) from
                                    (by
                                      unfold nb071_alpha_dummy_020;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb071_support_mem_0016)
                                              1)))) (show
                                    (nb071_alpha_dummy_015 x) ≠ (nb071_alpha_dummy_023 x) from
                                    (by
                                      unfold nb071_alpha_dummy_023;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb071_support_mem_0017 x)
                                              1)))) (TAlphaVar.there (show
                                      (nb071_alpha_dummy_013) ≠ (nb071_alpha_dummy_019) from (by
                                        unfold nb071_alpha_dummy_019;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb071_support_mem_0016)
                                                0)))) (show (nb071_alpha_dummy_015 x) ≠
                                        (nb071_alpha_dummy_022 x) from (by
                                        unfold nb071_alpha_dummy_022;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb071_support_mem_0017 x)
                                                0)))) (TAlphaVar.there (show
                                        (nb071_alpha_dummy_013) ≠ (nb071_alpha_dummy_017) from
                                        (by
                                          unfold nb071_alpha_dummy_017;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb071_support_mem_0014)
                                                  0)))) (show (nb071_alpha_dummy_015 x) ≠
        (nb071_alpha_dummy_018 x) from (by
                                          unfold nb071_alpha_dummy_018;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb071_support_mem_0015 x) 0))))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.refl_of_closed
                                    [((nb071_alpha_dummy_021), (nb071_alpha_dummy_024 x)),
                                      ((nb071_alpha_dummy_020), (nb071_alpha_dummy_023 x)),
                                      ((nb071_alpha_dummy_019), (nb071_alpha_dummy_022 x)),
                                      ((nb071_alpha_dummy_017), (nb071_alpha_dummy_018 x)),
                                      ((nb071_alpha_dummy_013), (nb071_alpha_dummy_015 x)),
                                      ((nb071_alpha_dummy_014), (nb071_alpha_dummy_016 x)),
                                      ((nb071_alpha_dummy_039), (nb071_alpha_dummy_040 x)),
                                      ((nb071_alpha_dummy_037), (nb071_alpha_dummy_038 x)),
                                      ((nb071_alpha_dummy_006), (nb071_alpha_dummy_008 x)),
                                      ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)),
                                      ((nb071_alpha_dummy_035), (nb071_alpha_dummy_036 x)),
                                      ((nb071_alpha_dummy_009), (nb071_alpha_dummy_010 x)),
                                      ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)),
                                      ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003),
                                        (nb071_alpha_dummy_004 x))]
                                    (syn_c1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb071_split_alpha_0002 x))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (show (nb071_alpha_dummy_013) ≠ (nb071_alpha_dummy_017) from (by
                              unfold nb071_alpha_dummy_017;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0014) 0))))
                          (show (nb071_alpha_dummy_015 x) ≠ (nb071_alpha_dummy_018 x) from (by
                              unfold nb071_alpha_dummy_018;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0015 x) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb071_alpha_dummy_017), (nb071_alpha_dummy_018 x)),
                          ((nb071_alpha_dummy_013), (nb071_alpha_dummy_015 x)),
                          ((nb071_alpha_dummy_014), (nb071_alpha_dummy_016 x)),
                          ((nb071_alpha_dummy_039), (nb071_alpha_dummy_040 x)),
                          ((nb071_alpha_dummy_037), (nb071_alpha_dummy_038 x)),
                          ((nb071_alpha_dummy_006), (nb071_alpha_dummy_008 x)),
                          ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)),
                          ((nb071_alpha_dummy_035), (nb071_alpha_dummy_036 x)),
                          ((nb071_alpha_dummy_009), (nb071_alpha_dummy_010 x)),
                          ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)),
                          ((nb071_alpha_dummy_000), x),
                          ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb071_alpha_dummy_013) ≠ (nb071_alpha_dummy_017) from (by
                            unfold nb071_alpha_dummy_017;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb071_support_mem_0014) 0))))
                        (show (nb071_alpha_dummy_015 x) ≠ (nb071_alpha_dummy_018 x) from (by
                            unfold nb071_alpha_dummy_018;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb071_support_mem_0015 x) 0))))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (show (nb071_alpha_dummy_013) ≠ (nb071_alpha_dummy_017) from (by
                              unfold nb071_alpha_dummy_017;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0014) 0))))
                          (show (nb071_alpha_dummy_015 x) ≠ (nb071_alpha_dummy_018 x) from (by
                              unfold nb071_alpha_dummy_018;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0015 x) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb071_alpha_dummy_017), (nb071_alpha_dummy_018 x)),
                          ((nb071_alpha_dummy_013), (nb071_alpha_dummy_015 x)),
                          ((nb071_alpha_dummy_014), (nb071_alpha_dummy_016 x)),
                          ((nb071_alpha_dummy_039), (nb071_alpha_dummy_040 x)),
                          ((nb071_alpha_dummy_037), (nb071_alpha_dummy_038 x)),
                          ((nb071_alpha_dummy_006), (nb071_alpha_dummy_008 x)),
                          ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)),
                          ((nb071_alpha_dummy_035), (nb071_alpha_dummy_036 x)),
                          ((nb071_alpha_dummy_009), (nb071_alpha_dummy_010 x)),
                          ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)),
                          ((nb071_alpha_dummy_000), x),
                          ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))

@[expose]
noncomputable def nb071_split_alpha_0004 (x : Var) :
    TAlphaWff
      [((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x),
        ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))]
      (Wff.classEq (Class.cv (nb071_alpha_dummy_003))
        (syn_cop (Class.cv (nb071_alpha_dummy_000)) (Class.cv (nb071_alpha_dummy_001))))
      (Wff.classEq (Class.cv (nb071_alpha_dummy_004 x))
        (syn_cop (Class.cv x) (Class.cv (nb071_alpha_dummy_002 x)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
          (show (nb071_alpha_dummy_001) ≠ (nb071_alpha_dummy_003) from (by
              unfold nb071_alpha_dummy_003;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0002) 0))))) (Ne.symm
          (show (nb071_alpha_dummy_002 x) ≠ (nb071_alpha_dummy_004 x) from (by
              unfold nb071_alpha_dummy_004;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0003 x) 0)))))
        (TAlphaVar.there (Ne.symm (show (nb071_alpha_dummy_000) ≠ (nb071_alpha_dummy_003) from
              (by
                unfold nb071_alpha_dummy_003;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0000) 0))))) (Ne.symm
            (show x ≠ (nb071_alpha_dummy_004 x) from (by
                unfold nb071_alpha_dummy_004;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0001 x) 0)))))
          (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (nb071_split_alpha_0001 x)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (nb071_split_alpha_0001 x)))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb071_alpha_dummy_001) ≠ (nb071_alpha_dummy_006) from (by
                                    unfold nb071_alpha_dummy_006;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb071_support_mem_0034) 1)))) (show
                                  (nb071_alpha_dummy_002 x) ≠ (nb071_alpha_dummy_008 x) from (by
                                    unfold nb071_alpha_dummy_008;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb071_support_mem_0036 x)
                                            1)))) (TAlphaVar.there
                                  (show (nb071_alpha_dummy_001) ≠ (nb071_alpha_dummy_005) from
                                    (by
                                      unfold nb071_alpha_dummy_005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb071_support_mem_0034)
                                              0)))) (show
                                    (nb071_alpha_dummy_002 x) ≠ (nb071_alpha_dummy_007 x) from
                                    (by
                                      unfold nb071_alpha_dummy_007;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb071_support_mem_0036 x)
                                              0)))) (TAlphaVar.there (show
                                      (nb071_alpha_dummy_001) ≠ (nb071_alpha_dummy_035) from (by
                                        unfold nb071_alpha_dummy_035;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb071_support_mem_0038)
                                                0)))) (show (nb071_alpha_dummy_002 x) ≠
                                        (nb071_alpha_dummy_036 x) from (by
                                        unfold nb071_alpha_dummy_036;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb071_support_mem_0039 x)
                                                0)))) (TAlphaVar.there (show
                                        (nb071_alpha_dummy_001) ≠ (nb071_alpha_dummy_009) from
                                        (by
                                          unfold nb071_alpha_dummy_009;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb071_support_mem_0035)
                                                  0)))) (show (nb071_alpha_dummy_002 x) ≠
        (nb071_alpha_dummy_010 x) from (by
                                          unfold nb071_alpha_dummy_010;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb071_support_mem_0037 x) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb071_alpha_dummy_000))).fv ∪
                                    ((Class.cv (nb071_alpha_dummy_001))).fv) (by decide))
                                (freshVar_injective (((Class.cv x)).fv ∪
                                    ((Class.cv (nb071_alpha_dummy_002 x))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.conj (nb071_split_alpha_0003 x)
        (nb071_split_alpha_0003 x))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb071_alpha_dummy_037),
        (nb071_alpha_dummy_038 x)), ((nb071_alpha_dummy_006), (nb071_alpha_dummy_008 x)),
                                        ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)),
                                        ((nb071_alpha_dummy_035), (nb071_alpha_dummy_036 x)),
                                        ((nb071_alpha_dummy_009), (nb071_alpha_dummy_010 x)),
                                        ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)),
                                        ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003),
        (nb071_alpha_dummy_004 x))] (syn_ccompl (syn_csn (syn_c0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb071_alpha_dummy_001) ≠ (nb071_alpha_dummy_006) from (by
                                    unfold nb071_alpha_dummy_006;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb071_support_mem_0034) 1)))) (show
                                  (nb071_alpha_dummy_002 x) ≠ (nb071_alpha_dummy_008 x) from (by
                                    unfold nb071_alpha_dummy_008;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb071_support_mem_0036 x)
                                            1)))) (TAlphaVar.there
                                  (show (nb071_alpha_dummy_001) ≠ (nb071_alpha_dummy_005) from
                                    (by
                                      unfold nb071_alpha_dummy_005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb071_support_mem_0034)
                                              0)))) (show
                                    (nb071_alpha_dummy_002 x) ≠ (nb071_alpha_dummy_007 x) from
                                    (by
                                      unfold nb071_alpha_dummy_007;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb071_support_mem_0036 x)
                                              0)))) (TAlphaVar.there (show
                                      (nb071_alpha_dummy_001) ≠ (nb071_alpha_dummy_035) from (by
                                        unfold nb071_alpha_dummy_035;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb071_support_mem_0038)
                                                0)))) (show (nb071_alpha_dummy_002 x) ≠
                                        (nb071_alpha_dummy_036 x) from (by
                                        unfold nb071_alpha_dummy_036;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb071_support_mem_0039 x)
                                                0)))) (TAlphaVar.there (show
                                        (nb071_alpha_dummy_001) ≠ (nb071_alpha_dummy_009) from
                                        (by
                                          unfold nb071_alpha_dummy_009;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb071_support_mem_0035)
                                                  0)))) (show (nb071_alpha_dummy_002 x) ≠
        (nb071_alpha_dummy_010 x) from (by
                                          unfold nb071_alpha_dummy_010;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb071_support_mem_0037 x) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb071_alpha_dummy_000))).fv ∪
                                    ((Class.cv (nb071_alpha_dummy_001))).fv) (by decide))
                                (freshVar_injective (((Class.cv x)).fv ∪
                                    ((Class.cv (nb071_alpha_dummy_002 x))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.conj (nb071_split_alpha_0003 x)
        (nb071_split_alpha_0003 x))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb071_alpha_dummy_037),
        (nb071_alpha_dummy_038 x)), ((nb071_alpha_dummy_006), (nb071_alpha_dummy_008 x)),
                                        ((nb071_alpha_dummy_005), (nb071_alpha_dummy_007 x)),
                                        ((nb071_alpha_dummy_035), (nb071_alpha_dummy_036 x)),
                                        ((nb071_alpha_dummy_009), (nb071_alpha_dummy_010 x)),
                                        ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)),
                                        ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003),
        (nb071_alpha_dummy_004 x))] (syn_ccompl (syn_csn (syn_c0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))))))))))

theorem nb071_compact_fv_empty_0032 : (nb071_alpha_dummy_041) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0106 : (nb071_alpha_dummy_041) ∉ ((syn_cncs)).fv := by
  simpa only [nb071_alpha_dummy_041, fv_syn_cncs] using (nb071_compact_fv_empty_0032)

theorem nb071_compact_fv_empty_0033 (x : Var) :
    (nb071_alpha_dummy_043 x) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0107 (x : Var) : (nb071_alpha_dummy_043 x) ∉ ((syn_cncs)).fv :=
  by simpa only [nb071_alpha_dummy_043, fv_syn_cncs] using (nb071_compact_fv_empty_0033 x)

theorem nb071_compact_fv_empty_0034 : (nb071_alpha_dummy_045) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0108 : (nb071_alpha_dummy_045) ∉ ((syn_cncs)).fv := by
  simpa only [nb071_alpha_dummy_045, fv_syn_cncs] using (nb071_compact_fv_empty_0034)

theorem nb071_compact_fv_empty_0035 (x : Var) :
    (nb071_alpha_dummy_046 x) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0109 (x : Var) : (nb071_alpha_dummy_046 x) ∉ ((syn_cncs)).fv :=
  by simpa only [nb071_alpha_dummy_046, fv_syn_cncs] using (nb071_compact_fv_empty_0035 x)

theorem nb071_compact_fv_empty_0036 : (nb071_alpha_dummy_048) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0110 : (nb071_alpha_dummy_048) ∉ ((syn_cncs)).fv := by
  simpa only [nb071_alpha_dummy_048, fv_syn_cncs] using (nb071_compact_fv_empty_0036)

theorem nb071_compact_fv_empty_0037 (x : Var) :
    (nb071_alpha_dummy_050 x) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0111 (x : Var) : (nb071_alpha_dummy_050 x) ∉ ((syn_cncs)).fv :=
  by simpa only [nb071_alpha_dummy_050, fv_syn_cncs] using (nb071_compact_fv_empty_0037 x)

theorem nb071_compact_fv_empty_0038 : (nb071_alpha_dummy_047) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0112 : (nb071_alpha_dummy_047) ∉ ((syn_cncs)).fv := by
  simpa only [nb071_alpha_dummy_047, fv_syn_cncs] using (nb071_compact_fv_empty_0038)

theorem nb071_compact_fv_empty_0039 (x : Var) :
    (nb071_alpha_dummy_049 x) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0113 (x : Var) : (nb071_alpha_dummy_049 x) ∉ ((syn_cncs)).fv :=
  by simpa only [nb071_alpha_dummy_049, fv_syn_cncs] using (nb071_compact_fv_empty_0039 x)

theorem nb071_wpp_notmem_0114 : (nb071_alpha_dummy_001) ∉ ((syn_cncs)).fv := by
  simpa only [nb071_alpha_dummy_001, fv_syn_cncs] using (nb071_compact_fv_empty_0020)

theorem nb071_wpp_notmem_0115 (x : Var) : (nb071_alpha_dummy_002 x) ∉ ((syn_cncs)).fv :=
  by simpa only [nb071_alpha_dummy_002, fv_syn_cncs] using (nb071_compact_fv_empty_0021 x)

theorem nb071_wpp_notmem_0116 : (nb071_alpha_dummy_000) ∉ ((syn_cncs)).fv := by
  simpa only [nb071_alpha_dummy_000, fv_syn_cncs] using (nb071_compact_fv_empty_0022)

theorem nb071_wpp_notmem_0117 (x : Var) : x ∉ ((syn_cncs)).fv := by
  simpa only [fv_syn_cncs] using (nb071_compact_fv_empty_0023 x)

theorem nb071_wpp_notmem_0118 : (nb071_alpha_dummy_003) ∉ ((syn_cncs)).fv := by
  simpa only [nb071_alpha_dummy_003, fv_syn_cncs] using (nb071_compact_fv_empty_0024)

theorem nb071_wpp_notmem_0119 (x : Var) : (nb071_alpha_dummy_004 x) ∉ ((syn_cncs)).fv :=
  by simpa only [nb071_alpha_dummy_004, fv_syn_cncs] using (nb071_compact_fv_empty_0025 x)

theorem nb071_compact_envfresh_0008 (x : Var) :
    TEnvFresh
      [((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)),
        ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)),
        ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)),
        ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)),
        ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)),
        ((nb071_alpha_dummy_000), x),
        ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))]
      ((syn_cncs)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb071_alpha_dummy_041) (nb071_alpha_dummy_043 x)
      (nb071_wpp_notmem_0106) (nb071_wpp_notmem_0107 x)
      (TEnvFresh.consFresh (nb071_alpha_dummy_045) (nb071_alpha_dummy_046 x)
        (nb071_wpp_notmem_0108) (nb071_wpp_notmem_0109 x)
        (TEnvFresh.consFresh (nb071_alpha_dummy_048) (nb071_alpha_dummy_050 x)
          (nb071_wpp_notmem_0110) (nb071_wpp_notmem_0111 x)
          (TEnvFresh.consFresh (nb071_alpha_dummy_047) (nb071_alpha_dummy_049 x)
            (nb071_wpp_notmem_0112) (nb071_wpp_notmem_0113 x)
            (TEnvFresh.consFresh (nb071_alpha_dummy_001) (nb071_alpha_dummy_002 x)
              (nb071_wpp_notmem_0114) (nb071_wpp_notmem_0115 x)
              (TEnvFresh.consFresh (nb071_alpha_dummy_000) x (nb071_wpp_notmem_0116)
                (nb071_wpp_notmem_0117 x)
                (TEnvFresh.consFresh (nb071_alpha_dummy_003) (nb071_alpha_dummy_004 x)
                  (nb071_wpp_notmem_0118) (nb071_wpp_notmem_0119 x)
                  (TEnvFresh.nil ((syn_cncs)).fv))))))))

@[expose]
noncomputable def nb071_wpp_refl_0008 (x : Var) :
    TReflOn
      [((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)),
        ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)),
        ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)),
        ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)),
        ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)),
        ((nb071_alpha_dummy_000), x),
        ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))]
      ((syn_cncs)).fv :=
  TEnvFresh.reflOn (nb071_compact_envfresh_0008 x)

theorem nb071_compact_fv_empty_0046 : (nb071_alpha_dummy_056) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb071_compact_fv_empty_0047 (x : Var) :
    (nb071_alpha_dummy_058 x) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb071_compact_fv_empty_0048 : (nb071_alpha_dummy_055) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb071_compact_fv_empty_0049 (x : Var) :
    (nb071_alpha_dummy_057 x) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb071_compact_fv_empty_0050 : (nb071_alpha_dummy_042) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb071_compact_fv_empty_0051 (x : Var) :
    (nb071_alpha_dummy_044 x) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
