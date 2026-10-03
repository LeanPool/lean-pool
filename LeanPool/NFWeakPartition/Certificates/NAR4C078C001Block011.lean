/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block010

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part035`. -/


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
noncomputable def nb078_split_alpha_0003 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_085), (nb078_alpha_dummy_086 f)),
        ((nb078_alpha_dummy_054), (nb078_alpha_dummy_056 f)),
        ((nb078_alpha_dummy_053), (nb078_alpha_dummy_055 f)),
        ((nb078_alpha_dummy_083), (nb078_alpha_dummy_084 f)),
        ((nb078_alpha_dummy_057), (nb078_alpha_dummy_058 f)),
        ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
        ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
        ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
        ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
        ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
        ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.classMem (Class.cv (nb078_alpha_dummy_085))
        (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_054)))))
      (Wff.classMem (Class.cv (nb078_alpha_dummy_086 f))
        (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_056 f))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
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
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_054) ≠ (nb078_alpha_dummy_087) from (by
                                unfold nb078_alpha_dummy_087;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0078) 0))))
                            (show (nb078_alpha_dummy_056 f) ≠ (nb078_alpha_dummy_088 f) from (by
                                unfold nb078_alpha_dummy_088;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0079 f) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_054) ≠ (nb078_alpha_dummy_085) from (by
                                  unfold nb078_alpha_dummy_085;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0076) 0))))
                              (show (nb078_alpha_dummy_056 f) ≠ (nb078_alpha_dummy_086 f) from
                                (by
                                  unfold nb078_alpha_dummy_086;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0077 f) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there
                        (freshVar_injective (((Class.cv (nb078_alpha_dummy_054))).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv (nb078_alpha_dummy_056 f))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078_alpha_dummy_061) ≠
        (nb078_alpha_dummy_068) from (by
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
                  (nb078_support_mem_0051 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_069), (nb078_alpha_dummy_072 f)), ((nb078_alpha_dummy_068),
        (nb078_alpha_dummy_071 f)), ((nb078_alpha_dummy_067), (nb078_alpha_dummy_070 f)),
        ((nb078_alpha_dummy_065), (nb078_alpha_dummy_066 f)), ((nb078_alpha_dummy_061),
        (nb078_alpha_dummy_063 f)), ((nb078_alpha_dummy_062), (nb078_alpha_dummy_064 f)),
        ((nb078_alpha_dummy_087), (nb078_alpha_dummy_088 f)), ((nb078_alpha_dummy_085),
        (nb078_alpha_dummy_086 f)), ((nb078_alpha_dummy_054), (nb078_alpha_dummy_056 f)),
        ((nb078_alpha_dummy_053), (nb078_alpha_dummy_055 f)), ((nb078_alpha_dummy_083),
        (nb078_alpha_dummy_084 f)), ((nb078_alpha_dummy_057), (nb078_alpha_dummy_058 f)),
        ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010),
        (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
        ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007),
        (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        ((nb078_alpha_dummy_087), (nb078_alpha_dummy_088 f)), ((nb078_alpha_dummy_085),
        (nb078_alpha_dummy_086 f)), ((nb078_alpha_dummy_054), (nb078_alpha_dummy_056 f)),
        ((nb078_alpha_dummy_053), (nb078_alpha_dummy_055 f)), ((nb078_alpha_dummy_083),
        (nb078_alpha_dummy_084 f)), ((nb078_alpha_dummy_057), (nb078_alpha_dummy_058 f)),
        ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010),
        (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
        ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007),
        (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_061))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_068) ≠ (nb078_alpha_dummy_079) from (by
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
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed
                                [((nb078_alpha_dummy_065), (nb078_alpha_dummy_066 f)),
                                  ((nb078_alpha_dummy_061), (nb078_alpha_dummy_063 f)),
                                  ((nb078_alpha_dummy_062), (nb078_alpha_dummy_064 f)),
                                  ((nb078_alpha_dummy_087), (nb078_alpha_dummy_088 f)),
                                  ((nb078_alpha_dummy_085), (nb078_alpha_dummy_086 f)),
                                  ((nb078_alpha_dummy_054), (nb078_alpha_dummy_056 f)),
                                  ((nb078_alpha_dummy_053), (nb078_alpha_dummy_055 f)),
                                  ((nb078_alpha_dummy_083), (nb078_alpha_dummy_084 f)),
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
                                (show (nb078_alpha_dummy_061) ≠ (nb078_alpha_dummy_065) from (by
                                    unfold nb078_alpha_dummy_065;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0050) 0)))) (show
                                  (nb078_alpha_dummy_063 f) ≠ (nb078_alpha_dummy_066 f) from (by
                                    unfold nb078_alpha_dummy_066;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0051 f)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
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
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed
                                [((nb078_alpha_dummy_065), (nb078_alpha_dummy_066 f)),
                                  ((nb078_alpha_dummy_061), (nb078_alpha_dummy_063 f)),
                                  ((nb078_alpha_dummy_062), (nb078_alpha_dummy_064 f)),
                                  ((nb078_alpha_dummy_087), (nb078_alpha_dummy_088 f)),
                                  ((nb078_alpha_dummy_085), (nb078_alpha_dummy_086 f)),
                                  ((nb078_alpha_dummy_054), (nb078_alpha_dummy_056 f)),
                                  ((nb078_alpha_dummy_053), (nb078_alpha_dummy_055 f)),
                                  ((nb078_alpha_dummy_083), (nb078_alpha_dummy_084 f)),
                                  ((nb078_alpha_dummy_057), (nb078_alpha_dummy_058 f)),
                                  ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
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
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_054) ≠ (nb078_alpha_dummy_087) from (by
                                unfold nb078_alpha_dummy_087;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0078) 0))))
                            (show (nb078_alpha_dummy_056 f) ≠ (nb078_alpha_dummy_088 f) from (by
                                unfold nb078_alpha_dummy_088;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0079 f) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_054) ≠ (nb078_alpha_dummy_085) from (by
                                  unfold nb078_alpha_dummy_085;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0076) 0))))
                              (show (nb078_alpha_dummy_056 f) ≠ (nb078_alpha_dummy_086 f) from
                                (by
                                  unfold nb078_alpha_dummy_086;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0077 f) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there
                        (freshVar_injective (((Class.cv (nb078_alpha_dummy_054))).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv (nb078_alpha_dummy_056 f))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078_alpha_dummy_061) ≠
        (nb078_alpha_dummy_068) from (by
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
                  (nb078_support_mem_0051 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_069), (nb078_alpha_dummy_072 f)), ((nb078_alpha_dummy_068),
        (nb078_alpha_dummy_071 f)), ((nb078_alpha_dummy_067), (nb078_alpha_dummy_070 f)),
        ((nb078_alpha_dummy_065), (nb078_alpha_dummy_066 f)), ((nb078_alpha_dummy_061),
        (nb078_alpha_dummy_063 f)), ((nb078_alpha_dummy_062), (nb078_alpha_dummy_064 f)),
        ((nb078_alpha_dummy_087), (nb078_alpha_dummy_088 f)), ((nb078_alpha_dummy_085),
        (nb078_alpha_dummy_086 f)), ((nb078_alpha_dummy_054), (nb078_alpha_dummy_056 f)),
        ((nb078_alpha_dummy_053), (nb078_alpha_dummy_055 f)), ((nb078_alpha_dummy_083),
        (nb078_alpha_dummy_084 f)), ((nb078_alpha_dummy_057), (nb078_alpha_dummy_058 f)),
        ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010),
        (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
        ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007),
        (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        ((nb078_alpha_dummy_087), (nb078_alpha_dummy_088 f)), ((nb078_alpha_dummy_085),
        (nb078_alpha_dummy_086 f)), ((nb078_alpha_dummy_054), (nb078_alpha_dummy_056 f)),
        ((nb078_alpha_dummy_053), (nb078_alpha_dummy_055 f)), ((nb078_alpha_dummy_083),
        (nb078_alpha_dummy_084 f)), ((nb078_alpha_dummy_057), (nb078_alpha_dummy_058 f)),
        ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010),
        (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
        ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007),
        (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_061))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_068) ≠ (nb078_alpha_dummy_079) from (by
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
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed
                                [((nb078_alpha_dummy_065), (nb078_alpha_dummy_066 f)),
                                  ((nb078_alpha_dummy_061), (nb078_alpha_dummy_063 f)),
                                  ((nb078_alpha_dummy_062), (nb078_alpha_dummy_064 f)),
                                  ((nb078_alpha_dummy_087), (nb078_alpha_dummy_088 f)),
                                  ((nb078_alpha_dummy_085), (nb078_alpha_dummy_086 f)),
                                  ((nb078_alpha_dummy_054), (nb078_alpha_dummy_056 f)),
                                  ((nb078_alpha_dummy_053), (nb078_alpha_dummy_055 f)),
                                  ((nb078_alpha_dummy_083), (nb078_alpha_dummy_084 f)),
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
                                (show (nb078_alpha_dummy_061) ≠ (nb078_alpha_dummy_065) from (by
                                    unfold nb078_alpha_dummy_065;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0050) 0)))) (show
                                  (nb078_alpha_dummy_063 f) ≠ (nb078_alpha_dummy_066 f) from (by
                                    unfold nb078_alpha_dummy_066;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0051 f)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
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
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed
                                [((nb078_alpha_dummy_065), (nb078_alpha_dummy_066 f)),
                                  ((nb078_alpha_dummy_061), (nb078_alpha_dummy_063 f)),
                                  ((nb078_alpha_dummy_062), (nb078_alpha_dummy_064 f)),
                                  ((nb078_alpha_dummy_087), (nb078_alpha_dummy_088 f)),
                                  ((nb078_alpha_dummy_085), (nb078_alpha_dummy_086 f)),
                                  ((nb078_alpha_dummy_054), (nb078_alpha_dummy_056 f)),
                                  ((nb078_alpha_dummy_053), (nb078_alpha_dummy_055 f)),
                                  ((nb078_alpha_dummy_083), (nb078_alpha_dummy_084 f)),
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


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part036`. -/


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
noncomputable def nb078_split_alpha_0004 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_101), (nb078_alpha_dummy_102 f)),
        ((nb078_alpha_dummy_099), (nb078_alpha_dummy_100 f)),
        ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)),
        ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)),
        ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)),
        ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
        ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
        ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
        ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
        ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
        ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_101))
          (Class.cab (nb078_alpha_dummy_095)
            (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_089))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_095))
                (syn_cphi (Class.cv (nb078_alpha_dummy_096))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_101)) (Class.cab (nb078_alpha_dummy_095)
              (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_089))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_095))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_096)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_102 f))
          (Class.cab (nb078_alpha_dummy_097 f)
            (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_091 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_098 f))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_102 f))
            (Class.cab (nb078_alpha_dummy_097 f)
              (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_091 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_098 f))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_089) ≠ (nb078_alpha_dummy_096) from
                    (by
                      unfold nb078_alpha_dummy_096;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0084) 1))))
                  (show (nb078_alpha_dummy_091 f) ≠ (nb078_alpha_dummy_098 f) from (by
                      unfold nb078_alpha_dummy_098;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0086 f) 1))))
                  (TAlphaVar.there (show (nb078_alpha_dummy_089) ≠ (nb078_alpha_dummy_095) from
                      (by
                        unfold nb078_alpha_dummy_095;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0084) 0))))
                    (show (nb078_alpha_dummy_091 f) ≠ (nb078_alpha_dummy_097 f) from (by
                        unfold nb078_alpha_dummy_097;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0086 f) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_089) ≠ (nb078_alpha_dummy_101) from (by
                          unfold nb078_alpha_dummy_101;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0088) 0))))
                      (show (nb078_alpha_dummy_091 f) ≠ (nb078_alpha_dummy_102 f) from (by
                          unfold nb078_alpha_dummy_102;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0089 f) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_089) ≠ (nb078_alpha_dummy_099) from (by
                            unfold nb078_alpha_dummy_099;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0085) 0))))
                        (show (nb078_alpha_dummy_091 f) ≠ (nb078_alpha_dummy_100 f) from (by
                            unfold nb078_alpha_dummy_100;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0087 f) 0))))
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_000))).fv)
                            (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_089))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_090))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078_alpha_dummy_091 f))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_092 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_096) ≠ (nb078_alpha_dummy_103) from (by
                              unfold nb078_alpha_dummy_103;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0090) 0))))
                          (show (nb078_alpha_dummy_098 f) ≠ (nb078_alpha_dummy_105 f) from (by
                              unfold nb078_alpha_dummy_105;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0091 f) 0))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_096) ≠ (nb078_alpha_dummy_104) from (by
                                unfold nb078_alpha_dummy_104;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0090) 1))))
                            (show (nb078_alpha_dummy_098 f) ≠ (nb078_alpha_dummy_106 f) from (by
                                unfold nb078_alpha_dummy_106;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0091 f) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_096))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_098 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_103) ≠ (nb078_alpha_dummy_110) from (by
          unfold nb078_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0094) 1)))) (show (nb078_alpha_dummy_105 f) ≠
        (nb078_alpha_dummy_113 f) from (by
          unfold nb078_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0095 f) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_103) ≠ (nb078_alpha_dummy_109) from (by
          unfold nb078_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0094) 0)))) (show (nb078_alpha_dummy_105 f) ≠
        (nb078_alpha_dummy_112 f) from (by
          unfold nb078_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0095 f) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_103) ≠ (nb078_alpha_dummy_107) from (by
          unfold nb078_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0092) 0)))) (show (nb078_alpha_dummy_105 f) ≠
        (nb078_alpha_dummy_108 f) from (by
          unfold nb078_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0093 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_111), (nb078_alpha_dummy_114 f)), ((nb078_alpha_dummy_110),
        (nb078_alpha_dummy_113 f)), ((nb078_alpha_dummy_109), (nb078_alpha_dummy_112 f)),
        ((nb078_alpha_dummy_107), (nb078_alpha_dummy_108 f)), ((nb078_alpha_dummy_103),
        (nb078_alpha_dummy_105 f)), ((nb078_alpha_dummy_104), (nb078_alpha_dummy_106 f)),
        ((nb078_alpha_dummy_096), (nb078_alpha_dummy_098 f)), ((nb078_alpha_dummy_095),
        (nb078_alpha_dummy_097 f)), ((nb078_alpha_dummy_101), (nb078_alpha_dummy_102 f)),
        ((nb078_alpha_dummy_099), (nb078_alpha_dummy_100 f)), ((nb078_alpha_dummy_090),
        (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)),
        ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011),
        (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
        ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015),
        (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
        ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_110) ≠ (nb078_alpha_dummy_117) from (by
          unfold
            nb078_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0098)
                  0)))) (show (nb078_alpha_dummy_113 f) ≠ (nb078_alpha_dummy_118 f) from (by
          unfold
            nb078_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_110) ≠ (nb078_alpha_dummy_115)
        from (by
          unfold
            nb078_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0096)
                  0)))) (show (nb078_alpha_dummy_113 f) ≠ (nb078_alpha_dummy_116 f) from (by
          unfold
            nb078_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_111) ≠ (nb078_alpha_dummy_117)
        from (by
          unfold
            nb078_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0102)
                  0)))) (show (nb078_alpha_dummy_114 f) ≠ (nb078_alpha_dummy_118 f) from (by
          unfold
            nb078_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_111) ≠ (nb078_alpha_dummy_115)
        from (by
          unfold
            nb078_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0100)
                  0)))) (show (nb078_alpha_dummy_114 f) ≠ (nb078_alpha_dummy_116 f) from (by
          unfold
            nb078_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_110) ≠ (nb078_alpha_dummy_117) from (by
          unfold
            nb078_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0098)
                  0)))) (show (nb078_alpha_dummy_113 f) ≠ (nb078_alpha_dummy_118 f) from (by
          unfold
            nb078_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_110) ≠ (nb078_alpha_dummy_115)
        from (by
          unfold
            nb078_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0096)
                  0)))) (show (nb078_alpha_dummy_113 f) ≠ (nb078_alpha_dummy_116 f) from (by
          unfold
            nb078_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_111) ≠ (nb078_alpha_dummy_117)
        from (by
          unfold
            nb078_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0102)
                  0)))) (show (nb078_alpha_dummy_114 f) ≠ (nb078_alpha_dummy_118 f) from (by
          unfold
            nb078_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_111) ≠ (nb078_alpha_dummy_115)
        from (by
          unfold
            nb078_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0100)
                  0)))) (show (nb078_alpha_dummy_114 f) ≠ (nb078_alpha_dummy_116 f) from (by
          unfold
            nb078_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_111), (nb078_alpha_dummy_114 f)), ((nb078_alpha_dummy_110),
        (nb078_alpha_dummy_113 f)), ((nb078_alpha_dummy_109), (nb078_alpha_dummy_112 f)),
        ((nb078_alpha_dummy_107), (nb078_alpha_dummy_108 f)), ((nb078_alpha_dummy_103),
        (nb078_alpha_dummy_105 f)), ((nb078_alpha_dummy_104), (nb078_alpha_dummy_106 f)),
        ((nb078_alpha_dummy_096), (nb078_alpha_dummy_098 f)), ((nb078_alpha_dummy_095),
        (nb078_alpha_dummy_097 f)), ((nb078_alpha_dummy_101), (nb078_alpha_dummy_102 f)),
        ((nb078_alpha_dummy_099), (nb078_alpha_dummy_100 f)), ((nb078_alpha_dummy_090),
        (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)),
        ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011),
        (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
        ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015),
        (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
        ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_103))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_110) ≠
        (nb078_alpha_dummy_121) from (by
          unfold
            nb078_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0106)
                  0)))) (show (nb078_alpha_dummy_113 f) ≠ (nb078_alpha_dummy_122 f) from (by
          unfold
            nb078_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_110) ≠ (nb078_alpha_dummy_119)
        from (by
          unfold
            nb078_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0104)
                  0)))) (show (nb078_alpha_dummy_113 f) ≠ (nb078_alpha_dummy_120 f) from (by
          unfold
            nb078_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_110) ≠ (nb078_alpha_dummy_121)
        from (by
          unfold
            nb078_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0106)
                  0)))) (show (nb078_alpha_dummy_113 f) ≠ (nb078_alpha_dummy_122 f) from (by
          unfold
            nb078_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_110) ≠ (nb078_alpha_dummy_119)
        from (by
          unfold
            nb078_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0104)
                  0)))) (show (nb078_alpha_dummy_113 f) ≠ (nb078_alpha_dummy_120 f) from (by
          unfold
            nb078_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_111) ≠ (nb078_alpha_dummy_123) from (by
          unfold
            nb078_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0110)
                  0)))) (show (nb078_alpha_dummy_114 f) ≠ (nb078_alpha_dummy_124 f) from (by
          unfold
            nb078_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_111) ≠ (nb078_alpha_dummy_119)
        from (by
          unfold
            nb078_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0108)
                  0)))) (show (nb078_alpha_dummy_114 f) ≠ (nb078_alpha_dummy_120 f) from (by
          unfold
            nb078_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_111) ≠
        (nb078_alpha_dummy_123) from (by
          unfold
            nb078_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0110)
                  0)))) (show (nb078_alpha_dummy_114 f) ≠ (nb078_alpha_dummy_124 f) from (by
          unfold
            nb078_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_111) ≠ (nb078_alpha_dummy_119)
        from (by
          unfold
            nb078_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0108)
                  0)))) (show (nb078_alpha_dummy_114 f) ≠ (nb078_alpha_dummy_120 f) from (by
          unfold
            nb078_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_103) ≠ (nb078_alpha_dummy_107) from (by
                                        unfold nb078_alpha_dummy_107;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0092)
                                                0)))) (show (nb078_alpha_dummy_105 f) ≠
                                        (nb078_alpha_dummy_108 f) from (by
                                        unfold nb078_alpha_dummy_108;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0093 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_107), (nb078_alpha_dummy_108 f)),
                                    ((nb078_alpha_dummy_103), (nb078_alpha_dummy_105 f)),
                                    ((nb078_alpha_dummy_104), (nb078_alpha_dummy_106 f)),
                                    ((nb078_alpha_dummy_096), (nb078_alpha_dummy_098 f)),
                                    ((nb078_alpha_dummy_095), (nb078_alpha_dummy_097 f)),
                                    ((nb078_alpha_dummy_101), (nb078_alpha_dummy_102 f)),
                                    ((nb078_alpha_dummy_099), (nb078_alpha_dummy_100 f)),
                                    ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)),
                                    ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)),
                                    ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)),
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
                                  (show (nb078_alpha_dummy_103) ≠ (nb078_alpha_dummy_107) from
                                    (by
                                      unfold nb078_alpha_dummy_107;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0092)
                                              0)))) (show
                                    (nb078_alpha_dummy_105 f) ≠ (nb078_alpha_dummy_108 f) from
                                    (by
                                      unfold nb078_alpha_dummy_108;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0093 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_103) ≠ (nb078_alpha_dummy_107) from (by
                                        unfold nb078_alpha_dummy_107;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0092)
                                                0)))) (show (nb078_alpha_dummy_105 f) ≠
                                        (nb078_alpha_dummy_108 f) from (by
                                        unfold nb078_alpha_dummy_108;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0093 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_107), (nb078_alpha_dummy_108 f)),
                                    ((nb078_alpha_dummy_103), (nb078_alpha_dummy_105 f)),
                                    ((nb078_alpha_dummy_104), (nb078_alpha_dummy_106 f)),
                                    ((nb078_alpha_dummy_096), (nb078_alpha_dummy_098 f)),
                                    ((nb078_alpha_dummy_095), (nb078_alpha_dummy_097 f)),
                                    ((nb078_alpha_dummy_101), (nb078_alpha_dummy_102 f)),
                                    ((nb078_alpha_dummy_099), (nb078_alpha_dummy_100 f)),
                                    ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)),
                                    ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)),
                                    ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)),
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
                  (TAlphaVar.there (show (nb078_alpha_dummy_089) ≠ (nb078_alpha_dummy_096) from
                      (by
                        unfold nb078_alpha_dummy_096;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0084) 1))))
                    (show (nb078_alpha_dummy_091 f) ≠ (nb078_alpha_dummy_098 f) from (by
                        unfold nb078_alpha_dummy_098;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0086 f) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_089) ≠ (nb078_alpha_dummy_095) from (by
                          unfold nb078_alpha_dummy_095;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0084) 0))))
                      (show (nb078_alpha_dummy_091 f) ≠ (nb078_alpha_dummy_097 f) from (by
                          unfold nb078_alpha_dummy_097;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0086 f) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_089) ≠ (nb078_alpha_dummy_101) from (by
                            unfold nb078_alpha_dummy_101;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0088) 0))))
                        (show (nb078_alpha_dummy_091 f) ≠ (nb078_alpha_dummy_102 f) from (by
                            unfold nb078_alpha_dummy_102;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0089 f) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_089) ≠ (nb078_alpha_dummy_099) from (by
                              unfold nb078_alpha_dummy_099;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0085) 0))))
                          (show (nb078_alpha_dummy_091 f) ≠ (nb078_alpha_dummy_100 f) from (by
                              unfold nb078_alpha_dummy_100;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0087 f) 0))))
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_000))).fv)
                              (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078_alpha_dummy_089))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_090))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_091 f))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_092 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_096) ≠ (nb078_alpha_dummy_103) from (by
                                unfold nb078_alpha_dummy_103;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0090) 0))))
                            (show (nb078_alpha_dummy_098 f) ≠ (nb078_alpha_dummy_105 f) from (by
                                unfold nb078_alpha_dummy_105;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0091 f) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_096) ≠ (nb078_alpha_dummy_104) from (by
                                  unfold nb078_alpha_dummy_104;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0090) 1))))
                              (show (nb078_alpha_dummy_098 f) ≠ (nb078_alpha_dummy_106 f) from
                                (by
                                  unfold nb078_alpha_dummy_106;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0091 f) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_096))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_098 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_103) ≠ (nb078_alpha_dummy_110) from (by
          unfold nb078_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0094) 1)))) (show (nb078_alpha_dummy_105 f) ≠
        (nb078_alpha_dummy_113 f) from (by
          unfold nb078_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0095 f) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_103) ≠ (nb078_alpha_dummy_109) from (by
          unfold nb078_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0094) 0)))) (show (nb078_alpha_dummy_105 f) ≠
        (nb078_alpha_dummy_112 f) from (by
          unfold nb078_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0095 f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_103) ≠ (nb078_alpha_dummy_107)
        from (by
          unfold nb078_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0092)
                  0)))) (show (nb078_alpha_dummy_105 f) ≠ (nb078_alpha_dummy_108 f) from (by
          unfold nb078_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0093 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_111), (nb078_alpha_dummy_114 f)), ((nb078_alpha_dummy_110),
        (nb078_alpha_dummy_113 f)), ((nb078_alpha_dummy_109), (nb078_alpha_dummy_112 f)),
        ((nb078_alpha_dummy_107), (nb078_alpha_dummy_108 f)), ((nb078_alpha_dummy_103),
        (nb078_alpha_dummy_105 f)), ((nb078_alpha_dummy_104), (nb078_alpha_dummy_106 f)),
        ((nb078_alpha_dummy_096), (nb078_alpha_dummy_098 f)), ((nb078_alpha_dummy_095),
        (nb078_alpha_dummy_097 f)), ((nb078_alpha_dummy_101), (nb078_alpha_dummy_102 f)),
        ((nb078_alpha_dummy_099), (nb078_alpha_dummy_100 f)), ((nb078_alpha_dummy_090),
        (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)),
        ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011),
        (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
        ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015),
        (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
        ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_110) ≠ (nb078_alpha_dummy_117) from (by
          unfold
            nb078_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0098)
                  0)))) (show (nb078_alpha_dummy_113 f) ≠ (nb078_alpha_dummy_118 f) from (by
          unfold
            nb078_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_110) ≠ (nb078_alpha_dummy_115)
        from (by
          unfold
            nb078_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0096)
                  0)))) (show (nb078_alpha_dummy_113 f) ≠ (nb078_alpha_dummy_116 f) from (by
          unfold
            nb078_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_111) ≠ (nb078_alpha_dummy_117)
        from (by
          unfold
            nb078_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0102)
                  0)))) (show (nb078_alpha_dummy_114 f) ≠ (nb078_alpha_dummy_118 f) from (by
          unfold
            nb078_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_111) ≠ (nb078_alpha_dummy_115)
        from (by
          unfold
            nb078_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0100)
                  0)))) (show (nb078_alpha_dummy_114 f) ≠ (nb078_alpha_dummy_116 f) from (by
          unfold
            nb078_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_110) ≠ (nb078_alpha_dummy_117) from (by
          unfold
            nb078_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0098)
                  0)))) (show (nb078_alpha_dummy_113 f) ≠ (nb078_alpha_dummy_118 f) from (by
          unfold
            nb078_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_110) ≠ (nb078_alpha_dummy_115)
        from (by
          unfold
            nb078_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0096)
                  0)))) (show (nb078_alpha_dummy_113 f) ≠ (nb078_alpha_dummy_116 f) from (by
          unfold
            nb078_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_111) ≠ (nb078_alpha_dummy_117)
        from (by
          unfold
            nb078_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0102)
                  0)))) (show (nb078_alpha_dummy_114 f) ≠ (nb078_alpha_dummy_118 f) from (by
          unfold
            nb078_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_111) ≠ (nb078_alpha_dummy_115)
        from (by
          unfold
            nb078_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0100)
                  0)))) (show (nb078_alpha_dummy_114 f) ≠ (nb078_alpha_dummy_116 f) from (by
          unfold
            nb078_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_111), (nb078_alpha_dummy_114 f)), ((nb078_alpha_dummy_110),
        (nb078_alpha_dummy_113 f)), ((nb078_alpha_dummy_109), (nb078_alpha_dummy_112 f)),
        ((nb078_alpha_dummy_107), (nb078_alpha_dummy_108 f)), ((nb078_alpha_dummy_103),
        (nb078_alpha_dummy_105 f)), ((nb078_alpha_dummy_104), (nb078_alpha_dummy_106 f)),
        ((nb078_alpha_dummy_096), (nb078_alpha_dummy_098 f)), ((nb078_alpha_dummy_095),
        (nb078_alpha_dummy_097 f)), ((nb078_alpha_dummy_101), (nb078_alpha_dummy_102 f)),
        ((nb078_alpha_dummy_099), (nb078_alpha_dummy_100 f)), ((nb078_alpha_dummy_090),
        (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)),
        ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011),
        (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
        ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015),
        (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
        ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_103))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_105
        f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_110) ≠
        (nb078_alpha_dummy_121) from (by
          unfold
            nb078_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0106)
                  0)))) (show (nb078_alpha_dummy_113 f) ≠ (nb078_alpha_dummy_122 f) from (by
          unfold
            nb078_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_110) ≠ (nb078_alpha_dummy_119)
        from (by
          unfold
            nb078_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0104)
                  0)))) (show (nb078_alpha_dummy_113 f) ≠ (nb078_alpha_dummy_120 f) from (by
          unfold
            nb078_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_110) ≠ (nb078_alpha_dummy_121)
        from (by
          unfold
            nb078_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0106)
                  0)))) (show (nb078_alpha_dummy_113 f) ≠ (nb078_alpha_dummy_122 f) from (by
          unfold
            nb078_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_110) ≠ (nb078_alpha_dummy_119)
        from (by
          unfold
            nb078_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0104)
                  0)))) (show (nb078_alpha_dummy_113 f) ≠ (nb078_alpha_dummy_120 f) from (by
          unfold
            nb078_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_111) ≠ (nb078_alpha_dummy_123) from (by
          unfold
            nb078_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0110)
                  0)))) (show (nb078_alpha_dummy_114 f) ≠ (nb078_alpha_dummy_124 f) from (by
          unfold
            nb078_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_111) ≠ (nb078_alpha_dummy_119)
        from (by
          unfold
            nb078_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0108)
                  0)))) (show (nb078_alpha_dummy_114 f) ≠ (nb078_alpha_dummy_120 f) from (by
          unfold
            nb078_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_111) ≠
        (nb078_alpha_dummy_123) from (by
          unfold
            nb078_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0110)
                  0)))) (show (nb078_alpha_dummy_114 f) ≠ (nb078_alpha_dummy_124 f) from (by
          unfold
            nb078_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_111) ≠ (nb078_alpha_dummy_119)
        from (by
          unfold
            nb078_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0108)
                  0)))) (show (nb078_alpha_dummy_114 f) ≠ (nb078_alpha_dummy_120 f) from (by
          unfold
            nb078_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_103) ≠ (nb078_alpha_dummy_107) from
                                        (by
                                          unfold nb078_alpha_dummy_107;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0092)
                                                  0)))) (show (nb078_alpha_dummy_105 f) ≠
        (nb078_alpha_dummy_108 f) from (by
                                          unfold nb078_alpha_dummy_108;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0093 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_107), (nb078_alpha_dummy_108 f)),
                                      ((nb078_alpha_dummy_103), (nb078_alpha_dummy_105 f)),
                                      ((nb078_alpha_dummy_104), (nb078_alpha_dummy_106 f)),
                                      ((nb078_alpha_dummy_096), (nb078_alpha_dummy_098 f)),
                                      ((nb078_alpha_dummy_095), (nb078_alpha_dummy_097 f)),
                                      ((nb078_alpha_dummy_101), (nb078_alpha_dummy_102 f)),
                                      ((nb078_alpha_dummy_099), (nb078_alpha_dummy_100 f)),
                                      ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)),
                                      ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)),
                                      ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)),
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
                                      (nb078_alpha_dummy_103) ≠ (nb078_alpha_dummy_107) from (by
                                        unfold nb078_alpha_dummy_107;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0092)
                                                0)))) (show (nb078_alpha_dummy_105 f) ≠
                                        (nb078_alpha_dummy_108 f) from (by
                                        unfold nb078_alpha_dummy_108;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0093 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_103) ≠ (nb078_alpha_dummy_107) from
                                        (by
                                          unfold nb078_alpha_dummy_107;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0092)
                                                  0)))) (show (nb078_alpha_dummy_105 f) ≠
        (nb078_alpha_dummy_108 f) from (by
                                          unfold nb078_alpha_dummy_108;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0093 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_107), (nb078_alpha_dummy_108 f)),
                                      ((nb078_alpha_dummy_103), (nb078_alpha_dummy_105 f)),
                                      ((nb078_alpha_dummy_104), (nb078_alpha_dummy_106 f)),
                                      ((nb078_alpha_dummy_096), (nb078_alpha_dummy_098 f)),
                                      ((nb078_alpha_dummy_095), (nb078_alpha_dummy_097 f)),
                                      ((nb078_alpha_dummy_101), (nb078_alpha_dummy_102 f)),
                                      ((nb078_alpha_dummy_099), (nb078_alpha_dummy_100 f)),
                                      ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)),
                                      ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)),
                                      ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)),
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

/-! Certificates from `NAR4C078C001Part037`. -/


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
noncomputable def nb078_split_alpha_0005 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_129), (nb078_alpha_dummy_130 f)),
        ((nb078_alpha_dummy_127), (nb078_alpha_dummy_128 f)),
        ((nb078_alpha_dummy_096), (nb078_alpha_dummy_098 f)),
        ((nb078_alpha_dummy_095), (nb078_alpha_dummy_097 f)),
        ((nb078_alpha_dummy_125), (nb078_alpha_dummy_126 f)),
        ((nb078_alpha_dummy_099), (nb078_alpha_dummy_100 f)),
        ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)),
        ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)),
        ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)),
        ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
        ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
        ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
        ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
        ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
        ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_129))
          (syn_cphi (Class.cv (nb078_alpha_dummy_096)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_129))
            (syn_cphi (Class.cv (nb078_alpha_dummy_096))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_130 f))
          (syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_130 f))
            (syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_096) ≠ (nb078_alpha_dummy_103) from
                    (by
                      unfold nb078_alpha_dummy_103;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0090) 0))))
                  (show (nb078_alpha_dummy_098 f) ≠ (nb078_alpha_dummy_105 f) from (by
                      unfold nb078_alpha_dummy_105;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0091 f) 0))))
                  (TAlphaVar.there (show (nb078_alpha_dummy_096) ≠ (nb078_alpha_dummy_104) from
                      (by
                        unfold nb078_alpha_dummy_104;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0090) 1))))
                    (show (nb078_alpha_dummy_098 f) ≠ (nb078_alpha_dummy_106 f) from (by
                        unfold nb078_alpha_dummy_106;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0091 f) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_096) ≠ (nb078_alpha_dummy_129) from (by
                          unfold nb078_alpha_dummy_129;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0120) 0))))
                      (show (nb078_alpha_dummy_098 f) ≠ (nb078_alpha_dummy_130 f) from (by
                          unfold nb078_alpha_dummy_130;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0121 f) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_096) ≠ (nb078_alpha_dummy_127) from (by
                            unfold nb078_alpha_dummy_127;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0118) 0))))
                        (show (nb078_alpha_dummy_098 f) ≠ (nb078_alpha_dummy_128 f) from (by
                            unfold nb078_alpha_dummy_128;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0119 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_096))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_098 f))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_103) ≠ (nb078_alpha_dummy_110) from (by
                                        unfold nb078_alpha_dummy_110;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0094)
                                                1)))) (show (nb078_alpha_dummy_105 f) ≠
                                        (nb078_alpha_dummy_113 f) from (by
                                        unfold nb078_alpha_dummy_113;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0095 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_103) ≠ (nb078_alpha_dummy_109) from
                                        (by
                                          unfold nb078_alpha_dummy_109;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0094)
                                                  0)))) (show (nb078_alpha_dummy_105 f) ≠
        (nb078_alpha_dummy_112 f) from (by
                                          unfold nb078_alpha_dummy_112;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0095 f) 0))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_103) ≠
        (nb078_alpha_dummy_107) from (by
          unfold nb078_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0092) 0)))) (show (nb078_alpha_dummy_105 f) ≠
        (nb078_alpha_dummy_108 f) from (by
          unfold nb078_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0093 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_111),
        (nb078_alpha_dummy_114 f)), ((nb078_alpha_dummy_110), (nb078_alpha_dummy_113 f)),
                                        ((nb078_alpha_dummy_109), (nb078_alpha_dummy_112 f)),
                                        ((nb078_alpha_dummy_107), (nb078_alpha_dummy_108 f)),
                                        ((nb078_alpha_dummy_103), (nb078_alpha_dummy_105 f)),
                                        ((nb078_alpha_dummy_104), (nb078_alpha_dummy_106 f)),
                                        ((nb078_alpha_dummy_129), (nb078_alpha_dummy_130 f)),
                                        ((nb078_alpha_dummy_127), (nb078_alpha_dummy_128 f)),
                                        ((nb078_alpha_dummy_096), (nb078_alpha_dummy_098 f)),
                                        ((nb078_alpha_dummy_095), (nb078_alpha_dummy_097 f)),
                                        ((nb078_alpha_dummy_125), (nb078_alpha_dummy_126 f)),
                                        ((nb078_alpha_dummy_099), (nb078_alpha_dummy_100 f)),
                                        ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)),
                                        ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)),
                                        ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)),
                                        ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
                                        ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
                                        ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
                                        ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
                                        ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
                                        ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
                                        ((nb078_alpha_dummy_000), f),
                                        ((nb078_alpha_dummy_004), y),
                                        ((nb078_alpha_dummy_003), x)]
                                      (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_110) ≠
        (nb078_alpha_dummy_117) from (by
          unfold
            nb078_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0098)
                  0)))) (show (nb078_alpha_dummy_113 f) ≠ (nb078_alpha_dummy_118 f) from (by
          unfold
            nb078_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_110) ≠ (nb078_alpha_dummy_115)
        from (by
          unfold
            nb078_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0096)
                  0)))) (show (nb078_alpha_dummy_113 f) ≠ (nb078_alpha_dummy_116 f) from (by
          unfold
            nb078_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_111) ≠ (nb078_alpha_dummy_117)
        from (by
          unfold
            nb078_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0102)
                  0)))) (show (nb078_alpha_dummy_114 f) ≠ (nb078_alpha_dummy_118 f) from (by
          unfold
            nb078_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_111) ≠ (nb078_alpha_dummy_115)
        from (by
          unfold
            nb078_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0100)
                  0)))) (show (nb078_alpha_dummy_114 f) ≠ (nb078_alpha_dummy_116 f) from (by
          unfold
            nb078_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_110) ≠ (nb078_alpha_dummy_117) from (by
          unfold
            nb078_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0098)
                  0)))) (show (nb078_alpha_dummy_113 f) ≠ (nb078_alpha_dummy_118 f) from (by
          unfold
            nb078_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_110) ≠ (nb078_alpha_dummy_115)
        from (by
          unfold
            nb078_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0096)
                  0)))) (show (nb078_alpha_dummy_113 f) ≠ (nb078_alpha_dummy_116 f) from (by
          unfold
            nb078_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_111) ≠ (nb078_alpha_dummy_117)
        from (by
          unfold
            nb078_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0102)
                  0)))) (show (nb078_alpha_dummy_114 f) ≠ (nb078_alpha_dummy_118 f) from (by
          unfold
            nb078_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_111) ≠ (nb078_alpha_dummy_115)
        from (by
          unfold
            nb078_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0100)
                  0)))) (show (nb078_alpha_dummy_114 f) ≠ (nb078_alpha_dummy_116 f) from (by
          unfold
            nb078_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb078_alpha_dummy_111), (nb078_alpha_dummy_114 f)),
        ((nb078_alpha_dummy_110), (nb078_alpha_dummy_113 f)), ((nb078_alpha_dummy_109),
        (nb078_alpha_dummy_112 f)), ((nb078_alpha_dummy_107), (nb078_alpha_dummy_108 f)),
        ((nb078_alpha_dummy_103), (nb078_alpha_dummy_105 f)), ((nb078_alpha_dummy_104),
        (nb078_alpha_dummy_106 f)), ((nb078_alpha_dummy_129), (nb078_alpha_dummy_130 f)),
        ((nb078_alpha_dummy_127), (nb078_alpha_dummy_128 f)), ((nb078_alpha_dummy_096),
        (nb078_alpha_dummy_098 f)), ((nb078_alpha_dummy_095), (nb078_alpha_dummy_097 f)),
        ((nb078_alpha_dummy_125), (nb078_alpha_dummy_126 f)), ((nb078_alpha_dummy_099),
        (nb078_alpha_dummy_100 f)), ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)),
        ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093),
        (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
        ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009),
        (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
        ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005),
        (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_110) ≠
        (nb078_alpha_dummy_121) from (by
          unfold
            nb078_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0106)
                  0)))) (show (nb078_alpha_dummy_113 f) ≠ (nb078_alpha_dummy_122 f) from (by
          unfold
            nb078_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_110) ≠ (nb078_alpha_dummy_119)
        from (by
          unfold
            nb078_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0104)
                  0)))) (show (nb078_alpha_dummy_113 f) ≠ (nb078_alpha_dummy_120 f) from (by
          unfold
            nb078_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_110) ≠ (nb078_alpha_dummy_121)
        from (by
          unfold
            nb078_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0106)
                  0)))) (show (nb078_alpha_dummy_113 f) ≠ (nb078_alpha_dummy_122 f) from (by
          unfold
            nb078_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_110) ≠ (nb078_alpha_dummy_119)
        from (by
          unfold
            nb078_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0104)
                  0)))) (show (nb078_alpha_dummy_113 f) ≠ (nb078_alpha_dummy_120 f) from (by
          unfold
            nb078_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_111) ≠ (nb078_alpha_dummy_123) from (by
          unfold
            nb078_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0110)
                  0)))) (show (nb078_alpha_dummy_114 f) ≠ (nb078_alpha_dummy_124 f) from (by
          unfold
            nb078_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_111) ≠ (nb078_alpha_dummy_119)
        from (by
          unfold
            nb078_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0108)
                  0)))) (show (nb078_alpha_dummy_114 f) ≠ (nb078_alpha_dummy_120 f) from (by
          unfold
            nb078_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_111) ≠
        (nb078_alpha_dummy_123) from (by
          unfold
            nb078_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0110)
                  0)))) (show (nb078_alpha_dummy_114 f) ≠ (nb078_alpha_dummy_124 f) from (by
          unfold
            nb078_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_111) ≠ (nb078_alpha_dummy_119)
        from (by
          unfold
            nb078_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0108)
                  0)))) (show (nb078_alpha_dummy_114 f) ≠ (nb078_alpha_dummy_120 f) from (by
          unfold
            nb078_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_103) ≠ (nb078_alpha_dummy_107) from (by
                                unfold nb078_alpha_dummy_107;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0092) 0))))
                            (show (nb078_alpha_dummy_105 f) ≠ (nb078_alpha_dummy_108 f) from (by
                                unfold nb078_alpha_dummy_108;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0093 f) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb078_alpha_dummy_107), (nb078_alpha_dummy_108 f)),
                            ((nb078_alpha_dummy_103), (nb078_alpha_dummy_105 f)),
                            ((nb078_alpha_dummy_104), (nb078_alpha_dummy_106 f)),
                            ((nb078_alpha_dummy_129), (nb078_alpha_dummy_130 f)),
                            ((nb078_alpha_dummy_127), (nb078_alpha_dummy_128 f)),
                            ((nb078_alpha_dummy_096), (nb078_alpha_dummy_098 f)),
                            ((nb078_alpha_dummy_095), (nb078_alpha_dummy_097 f)),
                            ((nb078_alpha_dummy_125), (nb078_alpha_dummy_126 f)),
                            ((nb078_alpha_dummy_099), (nb078_alpha_dummy_100 f)),
                            ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)),
                            ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)),
                            ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)),
                            ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
                            ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
                            ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
                            ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
                            ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
                            ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
                            ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
                            ((nb078_alpha_dummy_003), x)]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_103) ≠ (nb078_alpha_dummy_107) from (by
                              unfold nb078_alpha_dummy_107;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0092) 0))))
                          (show (nb078_alpha_dummy_105 f) ≠ (nb078_alpha_dummy_108 f) from (by
                              unfold nb078_alpha_dummy_108;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0093 f) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_103) ≠ (nb078_alpha_dummy_107) from (by
                                unfold nb078_alpha_dummy_107;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0092) 0))))
                            (show (nb078_alpha_dummy_105 f) ≠ (nb078_alpha_dummy_108 f) from (by
                                unfold nb078_alpha_dummy_108;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0093 f) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb078_alpha_dummy_107), (nb078_alpha_dummy_108 f)),
                            ((nb078_alpha_dummy_103), (nb078_alpha_dummy_105 f)),
                            ((nb078_alpha_dummy_104), (nb078_alpha_dummy_106 f)),
                            ((nb078_alpha_dummy_129), (nb078_alpha_dummy_130 f)),
                            ((nb078_alpha_dummy_127), (nb078_alpha_dummy_128 f)),
                            ((nb078_alpha_dummy_096), (nb078_alpha_dummy_098 f)),
                            ((nb078_alpha_dummy_095), (nb078_alpha_dummy_097 f)),
                            ((nb078_alpha_dummy_125), (nb078_alpha_dummy_126 f)),
                            ((nb078_alpha_dummy_099), (nb078_alpha_dummy_100 f)),
                            ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)),
                            ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)),
                            ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)),
                            ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
                            ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
                            ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
                            ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
                            ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
                            ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
                            ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
                            ((nb078_alpha_dummy_003), x)]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb078_alpha_dummy_096) ≠ (nb078_alpha_dummy_103) from (by
                        unfold nb078_alpha_dummy_103;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0090) 0))))
                    (show (nb078_alpha_dummy_098 f) ≠ (nb078_alpha_dummy_105 f) from (by
                        unfold nb078_alpha_dummy_105;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0091 f) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_096) ≠ (nb078_alpha_dummy_104) from (by
                          unfold nb078_alpha_dummy_104;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0090) 1))))
                      (show (nb078_alpha_dummy_098 f) ≠ (nb078_alpha_dummy_106 f) from (by
                          unfold nb078_alpha_dummy_106;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0091 f) 1))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_096) ≠ (nb078_alpha_dummy_129) from (by
                            unfold nb078_alpha_dummy_129;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0120) 0))))
                        (show (nb078_alpha_dummy_098 f) ≠ (nb078_alpha_dummy_130 f) from (by
                            unfold nb078_alpha_dummy_130;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0121 f) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_096) ≠ (nb078_alpha_dummy_127) from (by
                              unfold nb078_alpha_dummy_127;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0118) 0))))
                          (show (nb078_alpha_dummy_098 f) ≠ (nb078_alpha_dummy_128 f) from (by
                              unfold nb078_alpha_dummy_128;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0119 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_096))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_098 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb078_alpha_dummy_103) ≠ (nb078_alpha_dummy_110) from
                                        (by
                                          unfold nb078_alpha_dummy_110;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0094)
                                                  1)))) (show (nb078_alpha_dummy_105 f) ≠
        (nb078_alpha_dummy_113 f) from (by
                                          unfold nb078_alpha_dummy_113;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0095 f) 1))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_103) ≠
        (nb078_alpha_dummy_109) from (by
          unfold nb078_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0094) 0)))) (show (nb078_alpha_dummy_105 f) ≠
        (nb078_alpha_dummy_112 f) from (by
          unfold nb078_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0095 f) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_103) ≠ (nb078_alpha_dummy_107) from (by
          unfold nb078_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0092) 0)))) (show (nb078_alpha_dummy_105 f) ≠
        (nb078_alpha_dummy_108 f) from (by
          unfold nb078_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0093 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_111),
        (nb078_alpha_dummy_114 f)), ((nb078_alpha_dummy_110), (nb078_alpha_dummy_113 f)),
        ((nb078_alpha_dummy_109), (nb078_alpha_dummy_112 f)), ((nb078_alpha_dummy_107),
        (nb078_alpha_dummy_108 f)), ((nb078_alpha_dummy_103), (nb078_alpha_dummy_105 f)),
        ((nb078_alpha_dummy_104), (nb078_alpha_dummy_106 f)), ((nb078_alpha_dummy_129),
        (nb078_alpha_dummy_130 f)), ((nb078_alpha_dummy_127), (nb078_alpha_dummy_128 f)),
        ((nb078_alpha_dummy_096), (nb078_alpha_dummy_098 f)), ((nb078_alpha_dummy_095),
        (nb078_alpha_dummy_097 f)), ((nb078_alpha_dummy_125), (nb078_alpha_dummy_126 f)),
        ((nb078_alpha_dummy_099), (nb078_alpha_dummy_100 f)), ((nb078_alpha_dummy_090),
        (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)),
        ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011),
        (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
        ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015),
        (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
        ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
                                        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_110) ≠
        (nb078_alpha_dummy_117) from (by
          unfold
            nb078_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0098)
                  0)))) (show (nb078_alpha_dummy_113 f) ≠ (nb078_alpha_dummy_118 f) from (by
          unfold
            nb078_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_110) ≠ (nb078_alpha_dummy_115)
        from (by
          unfold
            nb078_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0096)
                  0)))) (show (nb078_alpha_dummy_113 f) ≠ (nb078_alpha_dummy_116 f) from (by
          unfold
            nb078_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_111) ≠ (nb078_alpha_dummy_117)
        from (by
          unfold
            nb078_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0102)
                  0)))) (show (nb078_alpha_dummy_114 f) ≠ (nb078_alpha_dummy_118 f) from (by
          unfold
            nb078_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_111) ≠ (nb078_alpha_dummy_115)
        from (by
          unfold
            nb078_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0100)
                  0)))) (show (nb078_alpha_dummy_114 f) ≠ (nb078_alpha_dummy_116 f) from (by
          unfold
            nb078_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_110) ≠ (nb078_alpha_dummy_117) from (by
          unfold
            nb078_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0098)
                  0)))) (show (nb078_alpha_dummy_113 f) ≠ (nb078_alpha_dummy_118 f) from (by
          unfold
            nb078_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_110) ≠ (nb078_alpha_dummy_115)
        from (by
          unfold
            nb078_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0096)
                  0)))) (show (nb078_alpha_dummy_113 f) ≠ (nb078_alpha_dummy_116 f) from (by
          unfold
            nb078_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_111) ≠ (nb078_alpha_dummy_117)
        from (by
          unfold
            nb078_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0102)
                  0)))) (show (nb078_alpha_dummy_114 f) ≠ (nb078_alpha_dummy_118 f) from (by
          unfold
            nb078_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_111) ≠ (nb078_alpha_dummy_115)
        from (by
          unfold
            nb078_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0100)
                  0)))) (show (nb078_alpha_dummy_114 f) ≠ (nb078_alpha_dummy_116 f) from (by
          unfold
            nb078_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_111), (nb078_alpha_dummy_114 f)), ((nb078_alpha_dummy_110),
        (nb078_alpha_dummy_113 f)), ((nb078_alpha_dummy_109), (nb078_alpha_dummy_112 f)),
        ((nb078_alpha_dummy_107), (nb078_alpha_dummy_108 f)), ((nb078_alpha_dummy_103),
        (nb078_alpha_dummy_105 f)), ((nb078_alpha_dummy_104), (nb078_alpha_dummy_106 f)),
        ((nb078_alpha_dummy_129), (nb078_alpha_dummy_130 f)), ((nb078_alpha_dummy_127),
        (nb078_alpha_dummy_128 f)), ((nb078_alpha_dummy_096), (nb078_alpha_dummy_098 f)),
        ((nb078_alpha_dummy_095), (nb078_alpha_dummy_097 f)), ((nb078_alpha_dummy_125),
        (nb078_alpha_dummy_126 f)), ((nb078_alpha_dummy_099), (nb078_alpha_dummy_100 f)),
        ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089),
        (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)),
        ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010),
        (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
        ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007),
        (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_110) ≠
        (nb078_alpha_dummy_121) from (by
          unfold
            nb078_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0106)
                  0)))) (show (nb078_alpha_dummy_113 f) ≠ (nb078_alpha_dummy_122 f) from (by
          unfold
            nb078_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_110) ≠ (nb078_alpha_dummy_119)
        from (by
          unfold
            nb078_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0104)
                  0)))) (show (nb078_alpha_dummy_113 f) ≠ (nb078_alpha_dummy_120 f) from (by
          unfold
            nb078_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_110) ≠ (nb078_alpha_dummy_121)
        from (by
          unfold
            nb078_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0106)
                  0)))) (show (nb078_alpha_dummy_113 f) ≠ (nb078_alpha_dummy_122 f) from (by
          unfold
            nb078_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_110) ≠ (nb078_alpha_dummy_119)
        from (by
          unfold
            nb078_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0104)
                  0)))) (show (nb078_alpha_dummy_113 f) ≠ (nb078_alpha_dummy_120 f) from (by
          unfold
            nb078_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_111) ≠ (nb078_alpha_dummy_123) from (by
          unfold
            nb078_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0110)
                  0)))) (show (nb078_alpha_dummy_114 f) ≠ (nb078_alpha_dummy_124 f) from (by
          unfold
            nb078_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_111) ≠ (nb078_alpha_dummy_119)
        from (by
          unfold
            nb078_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0108)
                  0)))) (show (nb078_alpha_dummy_114 f) ≠ (nb078_alpha_dummy_120 f) from (by
          unfold
            nb078_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_111) ≠
        (nb078_alpha_dummy_123) from (by
          unfold
            nb078_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0110)
                  0)))) (show (nb078_alpha_dummy_114 f) ≠ (nb078_alpha_dummy_124 f) from (by
          unfold
            nb078_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_111) ≠ (nb078_alpha_dummy_119)
        from (by
          unfold
            nb078_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0108)
                  0)))) (show (nb078_alpha_dummy_114 f) ≠ (nb078_alpha_dummy_120 f) from (by
          unfold
            nb078_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078_alpha_dummy_103) ≠ (nb078_alpha_dummy_107) from (by
                                  unfold nb078_alpha_dummy_107;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0092) 0))))
                              (show (nb078_alpha_dummy_105 f) ≠ (nb078_alpha_dummy_108 f) from
                                (by
                                  unfold nb078_alpha_dummy_108;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0093 f) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb078_alpha_dummy_107), (nb078_alpha_dummy_108 f)),
                              ((nb078_alpha_dummy_103), (nb078_alpha_dummy_105 f)),
                              ((nb078_alpha_dummy_104), (nb078_alpha_dummy_106 f)),
                              ((nb078_alpha_dummy_129), (nb078_alpha_dummy_130 f)),
                              ((nb078_alpha_dummy_127), (nb078_alpha_dummy_128 f)),
                              ((nb078_alpha_dummy_096), (nb078_alpha_dummy_098 f)),
                              ((nb078_alpha_dummy_095), (nb078_alpha_dummy_097 f)),
                              ((nb078_alpha_dummy_125), (nb078_alpha_dummy_126 f)),
                              ((nb078_alpha_dummy_099), (nb078_alpha_dummy_100 f)),
                              ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)),
                              ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)),
                              ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)),
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
                            (show (nb078_alpha_dummy_103) ≠ (nb078_alpha_dummy_107) from (by
                                unfold nb078_alpha_dummy_107;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0092) 0))))
                            (show (nb078_alpha_dummy_105 f) ≠ (nb078_alpha_dummy_108 f) from (by
                                unfold nb078_alpha_dummy_108;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0093 f) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078_alpha_dummy_103) ≠ (nb078_alpha_dummy_107) from (by
                                  unfold nb078_alpha_dummy_107;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0092) 0))))
                              (show (nb078_alpha_dummy_105 f) ≠ (nb078_alpha_dummy_108 f) from
                                (by
                                  unfold nb078_alpha_dummy_108;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0093 f) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb078_alpha_dummy_107), (nb078_alpha_dummy_108 f)),
                              ((nb078_alpha_dummy_103), (nb078_alpha_dummy_105 f)),
                              ((nb078_alpha_dummy_104), (nb078_alpha_dummy_106 f)),
                              ((nb078_alpha_dummy_129), (nb078_alpha_dummy_130 f)),
                              ((nb078_alpha_dummy_127), (nb078_alpha_dummy_128 f)),
                              ((nb078_alpha_dummy_096), (nb078_alpha_dummy_098 f)),
                              ((nb078_alpha_dummy_095), (nb078_alpha_dummy_097 f)),
                              ((nb078_alpha_dummy_125), (nb078_alpha_dummy_126 f)),
                              ((nb078_alpha_dummy_099), (nb078_alpha_dummy_100 f)),
                              ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)),
                              ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)),
                              ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)),
                              ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
                              ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
                              ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
                              ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
                              ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
                              ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
                              ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
                              ((nb078_alpha_dummy_003), x)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
