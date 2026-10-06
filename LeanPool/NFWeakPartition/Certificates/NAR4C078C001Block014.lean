/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block013

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part045`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0014`. -/
@[expose]
noncomputable def nb078SplitAlpha0014 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb078AlphaDummy085), (nb078AlphaDummy086 f)),
        ((nb078AlphaDummy054), (nb078AlphaDummy056 f)),
        ((nb078AlphaDummy053), (nb078AlphaDummy055 f)),
        ((nb078AlphaDummy083), (nb078AlphaDummy084 f)),
        ((nb078AlphaDummy057), (nb078AlphaDummy058 f)),
        ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
        ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
        ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
        ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.neg (synWa (Wff.classMem (Class.cv (nb078AlphaDummy085))
            (synCcompl (synCphi (Class.cv (nb078AlphaDummy054)))))
          (Wff.classMem (Class.cv (nb078AlphaDummy085)) (synCcompl (synCsn (synC0c))))))
      (Wff.neg (synWa (Wff.classMem (Class.cv (nb078AlphaDummy086 f))
            (synCcompl (synCphi (Class.cv (nb078AlphaDummy056 f)))))
          (Wff.classMem (Class.cv (nb078AlphaDummy086 f))
            (synCcompl (synCsn (synC0c)))))) :=
  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy054) ≠ (nb078AlphaDummy061) from (by
                                unfold nb078AlphaDummy061;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0048) 0))))
                            (show (nb078AlphaDummy056 f) ≠ (nb078AlphaDummy063 f) from (by
                                unfold nb078AlphaDummy063;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0049 f) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy054) ≠ (nb078AlphaDummy062) from (by
                                  unfold nb078AlphaDummy062;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0048) 1))))
                              (show (nb078AlphaDummy056 f) ≠ (nb078AlphaDummy064 f) from
                                (by
                                  unfold nb078AlphaDummy064;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0049 f) 1))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy054) ≠ (nb078AlphaDummy087) from (by
                                    unfold nb078AlphaDummy087;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0078) 0)))) (show
                                  (nb078AlphaDummy056 f) ≠ (nb078AlphaDummy088 f) from (by
                                    unfold nb078AlphaDummy088;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0079 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb078AlphaDummy054) ≠ (nb078AlphaDummy085) from
                                    (by
                                      unfold nb078AlphaDummy085;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0076)
                                              0)))) (show
                                    (nb078AlphaDummy056 f) ≠ (nb078AlphaDummy086 f) from
                                    (by
                                      unfold nb078AlphaDummy086;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0077 f)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy054))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy056 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy061) ≠ (nb078AlphaDummy068) from (by
          unfold nb078AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0052) 1)))) (show (nb078AlphaDummy063 f) ≠
        (nb078AlphaDummy071 f) from (by
          unfold nb078AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0053 f) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy061) ≠ (nb078AlphaDummy067) from (by
          unfold nb078AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0052) 0)))) (show (nb078AlphaDummy063 f) ≠
        (nb078AlphaDummy070 f) from (by
          unfold nb078AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0053 f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy061) ≠ (nb078AlphaDummy065)
        from (by
          unfold nb078AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0050)
                  0)))) (show (nb078AlphaDummy063 f) ≠ (nb078AlphaDummy066 f) from (by
          unfold nb078AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0051 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy069), (nb078AlphaDummy072 f)), ((nb078AlphaDummy068),
        (nb078AlphaDummy071 f)), ((nb078AlphaDummy067), (nb078AlphaDummy070 f)),
        ((nb078AlphaDummy065), (nb078AlphaDummy066 f)), ((nb078AlphaDummy061),
        (nb078AlphaDummy063 f)), ((nb078AlphaDummy062), (nb078AlphaDummy064 f)),
        ((nb078AlphaDummy087), (nb078AlphaDummy088 f)), ((nb078AlphaDummy085),
        (nb078AlphaDummy086 f)), ((nb078AlphaDummy054), (nb078AlphaDummy056 f)),
        ((nb078AlphaDummy053), (nb078AlphaDummy055 f)), ((nb078AlphaDummy083),
        (nb078AlphaDummy084 f)), ((nb078AlphaDummy057), (nb078AlphaDummy058 f)),
        ((nb078AlphaDummy011), (nb078AlphaDummy014 f)), ((nb078AlphaDummy010),
        (nb078AlphaDummy013 f)), ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
        ((nb078AlphaDummy015), (nb078AlphaDummy016 f)), ((nb078AlphaDummy000), f),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy068) ≠ (nb078AlphaDummy075) from (by
          unfold
            nb078AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0056)
                  0)))) (show (nb078AlphaDummy071 f) ≠ (nb078AlphaDummy076 f) from (by
          unfold
            nb078AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0057
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy068) ≠ (nb078AlphaDummy073)
        from (by
          unfold
            nb078AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0054)
                  0)))) (show (nb078AlphaDummy071 f) ≠ (nb078AlphaDummy074 f) from (by
          unfold
            nb078AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0055
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy061))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy063 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy069) ≠ (nb078AlphaDummy075)
        from (by
          unfold
            nb078AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0060)
                  0)))) (show (nb078AlphaDummy072 f) ≠ (nb078AlphaDummy076 f) from (by
          unfold
            nb078AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0061
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy069) ≠ (nb078AlphaDummy073)
        from (by
          unfold
            nb078AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0058)
                  0)))) (show (nb078AlphaDummy072 f) ≠ (nb078AlphaDummy074 f) from (by
          unfold
            nb078AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0059
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy068) ≠ (nb078AlphaDummy075) from (by
          unfold
            nb078AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0056)
                  0)))) (show (nb078AlphaDummy071 f) ≠ (nb078AlphaDummy076 f) from (by
          unfold
            nb078AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0057
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy068) ≠ (nb078AlphaDummy073)
        from (by
          unfold
            nb078AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0054)
                  0)))) (show (nb078AlphaDummy071 f) ≠ (nb078AlphaDummy074 f) from (by
          unfold
            nb078AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0055
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy061))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy063 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy069) ≠ (nb078AlphaDummy075)
        from (by
          unfold
            nb078AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0060)
                  0)))) (show (nb078AlphaDummy072 f) ≠ (nb078AlphaDummy076 f) from (by
          unfold
            nb078AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0061
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy069) ≠ (nb078AlphaDummy073)
        from (by
          unfold
            nb078AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0058)
                  0)))) (show (nb078AlphaDummy072 f) ≠ (nb078AlphaDummy074 f) from (by
          unfold
            nb078AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0059
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy069), (nb078AlphaDummy072 f)), ((nb078AlphaDummy068),
        (nb078AlphaDummy071 f)), ((nb078AlphaDummy067), (nb078AlphaDummy070 f)),
        ((nb078AlphaDummy065), (nb078AlphaDummy066 f)), ((nb078AlphaDummy061),
        (nb078AlphaDummy063 f)), ((nb078AlphaDummy062), (nb078AlphaDummy064 f)),
        ((nb078AlphaDummy087), (nb078AlphaDummy088 f)), ((nb078AlphaDummy085),
        (nb078AlphaDummy086 f)), ((nb078AlphaDummy054), (nb078AlphaDummy056 f)),
        ((nb078AlphaDummy053), (nb078AlphaDummy055 f)), ((nb078AlphaDummy083),
        (nb078AlphaDummy084 f)), ((nb078AlphaDummy057), (nb078AlphaDummy058 f)),
        ((nb078AlphaDummy011), (nb078AlphaDummy014 f)), ((nb078AlphaDummy010),
        (nb078AlphaDummy013 f)), ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
        ((nb078AlphaDummy015), (nb078AlphaDummy016 f)), ((nb078AlphaDummy000), f),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy061))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy063
        f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy061))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy063 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy068) ≠
        (nb078AlphaDummy079) from (by
          unfold
            nb078AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0064)
                  0)))) (show (nb078AlphaDummy071 f) ≠ (nb078AlphaDummy080 f) from (by
          unfold
            nb078AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0065
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy068) ≠ (nb078AlphaDummy077)
        from (by
          unfold
            nb078AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0062)
                  0)))) (show (nb078AlphaDummy071 f) ≠ (nb078AlphaDummy078 f) from (by
          unfold
            nb078AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0063
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy061))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy063 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy068) ≠ (nb078AlphaDummy079)
        from (by
          unfold
            nb078AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0064)
                  0)))) (show (nb078AlphaDummy071 f) ≠ (nb078AlphaDummy080 f) from (by
          unfold
            nb078AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0065
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy068) ≠ (nb078AlphaDummy077)
        from (by
          unfold
            nb078AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0062)
                  0)))) (show (nb078AlphaDummy071 f) ≠ (nb078AlphaDummy078 f) from (by
          unfold
            nb078AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0063
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy061))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy063 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy069) ≠ (nb078AlphaDummy081) from (by
          unfold
            nb078AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0068)
                  0)))) (show (nb078AlphaDummy072 f) ≠ (nb078AlphaDummy082 f) from (by
          unfold
            nb078AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0069
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy069) ≠ (nb078AlphaDummy077)
        from (by
          unfold
            nb078AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0066)
                  0)))) (show (nb078AlphaDummy072 f) ≠ (nb078AlphaDummy078 f) from (by
          unfold
            nb078AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0067
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy069) ≠
        (nb078AlphaDummy081) from (by
          unfold
            nb078AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0068)
                  0)))) (show (nb078AlphaDummy072 f) ≠ (nb078AlphaDummy082 f) from (by
          unfold
            nb078AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0069
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy069) ≠ (nb078AlphaDummy077)
        from (by
          unfold
            nb078AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0066)
                  0)))) (show (nb078AlphaDummy072 f) ≠ (nb078AlphaDummy078 f) from (by
          unfold
            nb078AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0067
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy061) ≠ (nb078AlphaDummy065) from
                                        (by
                                          unfold nb078AlphaDummy065;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0050)
                                                  0)))) (show (nb078AlphaDummy063 f) ≠
        (nb078AlphaDummy066 f) from (by
                                          unfold nb078AlphaDummy066;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0051 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy065), (nb078AlphaDummy066 f)),
                                      ((nb078AlphaDummy061), (nb078AlphaDummy063 f)),
                                      ((nb078AlphaDummy062), (nb078AlphaDummy064 f)),
                                      ((nb078AlphaDummy087), (nb078AlphaDummy088 f)),
                                      ((nb078AlphaDummy085), (nb078AlphaDummy086 f)),
                                      ((nb078AlphaDummy054), (nb078AlphaDummy056 f)),
                                      ((nb078AlphaDummy053), (nb078AlphaDummy055 f)),
                                      ((nb078AlphaDummy083), (nb078AlphaDummy084 f)),
                                      ((nb078AlphaDummy057), (nb078AlphaDummy058 f)),
                                      ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
                                      ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                                      ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                                      ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
                                      ((nb078AlphaDummy000), f),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy061) ≠ (nb078AlphaDummy065) from (by
                                        unfold nb078AlphaDummy065;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0050)
                                                0)))) (show (nb078AlphaDummy063 f) ≠
                                        (nb078AlphaDummy066 f) from (by
                                        unfold nb078AlphaDummy066;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0051 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy061) ≠ (nb078AlphaDummy065) from
                                        (by
                                          unfold nb078AlphaDummy065;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0050)
                                                  0)))) (show (nb078AlphaDummy063 f) ≠
        (nb078AlphaDummy066 f) from (by
                                          unfold nb078AlphaDummy066;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0051 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy065), (nb078AlphaDummy066 f)),
                                      ((nb078AlphaDummy061), (nb078AlphaDummy063 f)),
                                      ((nb078AlphaDummy062), (nb078AlphaDummy064 f)),
                                      ((nb078AlphaDummy087), (nb078AlphaDummy088 f)),
                                      ((nb078AlphaDummy085), (nb078AlphaDummy086 f)),
                                      ((nb078AlphaDummy054), (nb078AlphaDummy056 f)),
                                      ((nb078AlphaDummy053), (nb078AlphaDummy055 f)),
                                      ((nb078AlphaDummy083), (nb078AlphaDummy084 f)),
                                      ((nb078AlphaDummy057), (nb078AlphaDummy058 f)),
                                      ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
                                      ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                                      ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                                      ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
                                      ((nb078AlphaDummy000), f),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy054) ≠ (nb078AlphaDummy061) from (by
                                unfold nb078AlphaDummy061;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0048) 0))))
                            (show (nb078AlphaDummy056 f) ≠ (nb078AlphaDummy063 f) from (by
                                unfold nb078AlphaDummy063;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0049 f) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy054) ≠ (nb078AlphaDummy062) from (by
                                  unfold nb078AlphaDummy062;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0048) 1))))
                              (show (nb078AlphaDummy056 f) ≠ (nb078AlphaDummy064 f) from
                                (by
                                  unfold nb078AlphaDummy064;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0049 f) 1))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy054) ≠ (nb078AlphaDummy087) from (by
                                    unfold nb078AlphaDummy087;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0078) 0)))) (show
                                  (nb078AlphaDummy056 f) ≠ (nb078AlphaDummy088 f) from (by
                                    unfold nb078AlphaDummy088;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0079 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb078AlphaDummy054) ≠ (nb078AlphaDummy085) from
                                    (by
                                      unfold nb078AlphaDummy085;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0076)
                                              0)))) (show
                                    (nb078AlphaDummy056 f) ≠ (nb078AlphaDummy086 f) from
                                    (by
                                      unfold nb078AlphaDummy086;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0077 f)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy054))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy056 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy061) ≠ (nb078AlphaDummy068) from (by
          unfold nb078AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0052) 1)))) (show (nb078AlphaDummy063 f) ≠
        (nb078AlphaDummy071 f) from (by
          unfold nb078AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0053 f) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy061) ≠ (nb078AlphaDummy067) from (by
          unfold nb078AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0052) 0)))) (show (nb078AlphaDummy063 f) ≠
        (nb078AlphaDummy070 f) from (by
          unfold nb078AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0053 f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy061) ≠ (nb078AlphaDummy065)
        from (by
          unfold nb078AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0050)
                  0)))) (show (nb078AlphaDummy063 f) ≠ (nb078AlphaDummy066 f) from (by
          unfold nb078AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0051 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy069), (nb078AlphaDummy072 f)), ((nb078AlphaDummy068),
        (nb078AlphaDummy071 f)), ((nb078AlphaDummy067), (nb078AlphaDummy070 f)),
        ((nb078AlphaDummy065), (nb078AlphaDummy066 f)), ((nb078AlphaDummy061),
        (nb078AlphaDummy063 f)), ((nb078AlphaDummy062), (nb078AlphaDummy064 f)),
        ((nb078AlphaDummy087), (nb078AlphaDummy088 f)), ((nb078AlphaDummy085),
        (nb078AlphaDummy086 f)), ((nb078AlphaDummy054), (nb078AlphaDummy056 f)),
        ((nb078AlphaDummy053), (nb078AlphaDummy055 f)), ((nb078AlphaDummy083),
        (nb078AlphaDummy084 f)), ((nb078AlphaDummy057), (nb078AlphaDummy058 f)),
        ((nb078AlphaDummy011), (nb078AlphaDummy014 f)), ((nb078AlphaDummy010),
        (nb078AlphaDummy013 f)), ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
        ((nb078AlphaDummy015), (nb078AlphaDummy016 f)), ((nb078AlphaDummy000), f),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy068) ≠ (nb078AlphaDummy075) from (by
          unfold
            nb078AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0056)
                  0)))) (show (nb078AlphaDummy071 f) ≠ (nb078AlphaDummy076 f) from (by
          unfold
            nb078AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0057
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy068) ≠ (nb078AlphaDummy073)
        from (by
          unfold
            nb078AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0054)
                  0)))) (show (nb078AlphaDummy071 f) ≠ (nb078AlphaDummy074 f) from (by
          unfold
            nb078AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0055
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy061))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy063 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy069) ≠ (nb078AlphaDummy075)
        from (by
          unfold
            nb078AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0060)
                  0)))) (show (nb078AlphaDummy072 f) ≠ (nb078AlphaDummy076 f) from (by
          unfold
            nb078AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0061
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy069) ≠ (nb078AlphaDummy073)
        from (by
          unfold
            nb078AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0058)
                  0)))) (show (nb078AlphaDummy072 f) ≠ (nb078AlphaDummy074 f) from (by
          unfold
            nb078AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0059
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy068) ≠ (nb078AlphaDummy075) from (by
          unfold
            nb078AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0056)
                  0)))) (show (nb078AlphaDummy071 f) ≠ (nb078AlphaDummy076 f) from (by
          unfold
            nb078AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0057
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy068) ≠ (nb078AlphaDummy073)
        from (by
          unfold
            nb078AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0054)
                  0)))) (show (nb078AlphaDummy071 f) ≠ (nb078AlphaDummy074 f) from (by
          unfold
            nb078AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0055
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy061))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy063 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy069) ≠ (nb078AlphaDummy075)
        from (by
          unfold
            nb078AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0060)
                  0)))) (show (nb078AlphaDummy072 f) ≠ (nb078AlphaDummy076 f) from (by
          unfold
            nb078AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0061
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy069) ≠ (nb078AlphaDummy073)
        from (by
          unfold
            nb078AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0058)
                  0)))) (show (nb078AlphaDummy072 f) ≠ (nb078AlphaDummy074 f) from (by
          unfold
            nb078AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0059
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy069), (nb078AlphaDummy072 f)), ((nb078AlphaDummy068),
        (nb078AlphaDummy071 f)), ((nb078AlphaDummy067), (nb078AlphaDummy070 f)),
        ((nb078AlphaDummy065), (nb078AlphaDummy066 f)), ((nb078AlphaDummy061),
        (nb078AlphaDummy063 f)), ((nb078AlphaDummy062), (nb078AlphaDummy064 f)),
        ((nb078AlphaDummy087), (nb078AlphaDummy088 f)), ((nb078AlphaDummy085),
        (nb078AlphaDummy086 f)), ((nb078AlphaDummy054), (nb078AlphaDummy056 f)),
        ((nb078AlphaDummy053), (nb078AlphaDummy055 f)), ((nb078AlphaDummy083),
        (nb078AlphaDummy084 f)), ((nb078AlphaDummy057), (nb078AlphaDummy058 f)),
        ((nb078AlphaDummy011), (nb078AlphaDummy014 f)), ((nb078AlphaDummy010),
        (nb078AlphaDummy013 f)), ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
        ((nb078AlphaDummy015), (nb078AlphaDummy016 f)), ((nb078AlphaDummy000), f),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy061))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy063
        f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy061))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy063 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy068) ≠
        (nb078AlphaDummy079) from (by
          unfold
            nb078AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0064)
                  0)))) (show (nb078AlphaDummy071 f) ≠ (nb078AlphaDummy080 f) from (by
          unfold
            nb078AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0065
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy068) ≠ (nb078AlphaDummy077)
        from (by
          unfold
            nb078AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0062)
                  0)))) (show (nb078AlphaDummy071 f) ≠ (nb078AlphaDummy078 f) from (by
          unfold
            nb078AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0063
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy061))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy063 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy068) ≠ (nb078AlphaDummy079)
        from (by
          unfold
            nb078AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0064)
                  0)))) (show (nb078AlphaDummy071 f) ≠ (nb078AlphaDummy080 f) from (by
          unfold
            nb078AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0065
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy068) ≠ (nb078AlphaDummy077)
        from (by
          unfold
            nb078AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0062)
                  0)))) (show (nb078AlphaDummy071 f) ≠ (nb078AlphaDummy078 f) from (by
          unfold
            nb078AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0063
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy061))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy063 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy069) ≠ (nb078AlphaDummy081) from (by
          unfold
            nb078AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0068)
                  0)))) (show (nb078AlphaDummy072 f) ≠ (nb078AlphaDummy082 f) from (by
          unfold
            nb078AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0069
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy069) ≠ (nb078AlphaDummy077)
        from (by
          unfold
            nb078AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0066)
                  0)))) (show (nb078AlphaDummy072 f) ≠ (nb078AlphaDummy078 f) from (by
          unfold
            nb078AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0067
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy069) ≠
        (nb078AlphaDummy081) from (by
          unfold
            nb078AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0068)
                  0)))) (show (nb078AlphaDummy072 f) ≠ (nb078AlphaDummy082 f) from (by
          unfold
            nb078AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0069
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy069) ≠ (nb078AlphaDummy077)
        from (by
          unfold
            nb078AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0066)
                  0)))) (show (nb078AlphaDummy072 f) ≠ (nb078AlphaDummy078 f) from (by
          unfold
            nb078AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0067
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy061) ≠ (nb078AlphaDummy065) from
                                        (by
                                          unfold nb078AlphaDummy065;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0050)
                                                  0)))) (show (nb078AlphaDummy063 f) ≠
        (nb078AlphaDummy066 f) from (by
                                          unfold nb078AlphaDummy066;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0051 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy065), (nb078AlphaDummy066 f)),
                                      ((nb078AlphaDummy061), (nb078AlphaDummy063 f)),
                                      ((nb078AlphaDummy062), (nb078AlphaDummy064 f)),
                                      ((nb078AlphaDummy087), (nb078AlphaDummy088 f)),
                                      ((nb078AlphaDummy085), (nb078AlphaDummy086 f)),
                                      ((nb078AlphaDummy054), (nb078AlphaDummy056 f)),
                                      ((nb078AlphaDummy053), (nb078AlphaDummy055 f)),
                                      ((nb078AlphaDummy083), (nb078AlphaDummy084 f)),
                                      ((nb078AlphaDummy057), (nb078AlphaDummy058 f)),
                                      ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
                                      ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                                      ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                                      ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
                                      ((nb078AlphaDummy000), f),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy061) ≠ (nb078AlphaDummy065) from (by
                                        unfold nb078AlphaDummy065;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0050)
                                                0)))) (show (nb078AlphaDummy063 f) ≠
                                        (nb078AlphaDummy066 f) from (by
                                        unfold nb078AlphaDummy066;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0051 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy061) ≠ (nb078AlphaDummy065) from
                                        (by
                                          unfold nb078AlphaDummy065;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0050)
                                                  0)))) (show (nb078AlphaDummy063 f) ≠
        (nb078AlphaDummy066 f) from (by
                                          unfold nb078AlphaDummy066;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0051 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy065), (nb078AlphaDummy066 f)),
                                      ((nb078AlphaDummy061), (nb078AlphaDummy063 f)),
                                      ((nb078AlphaDummy062), (nb078AlphaDummy064 f)),
                                      ((nb078AlphaDummy087), (nb078AlphaDummy088 f)),
                                      ((nb078AlphaDummy085), (nb078AlphaDummy086 f)),
                                      ((nb078AlphaDummy054), (nb078AlphaDummy056 f)),
                                      ((nb078AlphaDummy053), (nb078AlphaDummy055 f)),
                                      ((nb078AlphaDummy083), (nb078AlphaDummy084 f)),
                                      ((nb078AlphaDummy057), (nb078AlphaDummy058 f)),
                                      ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
                                      ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                                      ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                                      ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
                                      ((nb078AlphaDummy000), f),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
          [((nb078AlphaDummy085), (nb078AlphaDummy086 f)),
            ((nb078AlphaDummy054), (nb078AlphaDummy056 f)),
            ((nb078AlphaDummy053), (nb078AlphaDummy055 f)),
            ((nb078AlphaDummy083), (nb078AlphaDummy084 f)),
            ((nb078AlphaDummy057), (nb078AlphaDummy058 f)),
            ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
            ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
            ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
            ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
            ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
            ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part046`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0015`. -/
@[expose]
noncomputable def nb078SplitAlpha0015 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb078AlphaDummy101), (nb078AlphaDummy102 f)),
        ((nb078AlphaDummy099), (nb078AlphaDummy100 f)),
        ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
        ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
        ((nb078AlphaDummy093), (nb078AlphaDummy094 f)),
        ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
        ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
        ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
        ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy101))
          (Class.cab (nb078AlphaDummy095)
            (synWrex (nb078AlphaDummy096) (Class.cv (nb078AlphaDummy089))
              (Wff.classEq (Class.cv (nb078AlphaDummy095))
                (synCphi (Class.cv (nb078AlphaDummy096))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy101)) (Class.cab (nb078AlphaDummy095)
              (synWrex (nb078AlphaDummy096) (Class.cv (nb078AlphaDummy089))
                (Wff.classEq (Class.cv (nb078AlphaDummy095))
                  (synCphi (Class.cv (nb078AlphaDummy096)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy102 f))
          (Class.cab (nb078AlphaDummy097 f)
            (synWrex (nb078AlphaDummy098 f) (Class.cv (nb078AlphaDummy091 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy097 f))
                (synCphi (Class.cv (nb078AlphaDummy098 f))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy102 f))
            (Class.cab (nb078AlphaDummy097 f)
              (synWrex (nb078AlphaDummy098 f) (Class.cv (nb078AlphaDummy091 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy097 f))
                  (synCphi (Class.cv (nb078AlphaDummy098 f))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy096) from
                    (by
                      unfold nb078AlphaDummy096;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0084) 1))))
                  (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy098 f) from (by
                      unfold nb078AlphaDummy098;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0086 f) 1))))
                  (TAlphaVar.there (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy095) from
                      (by
                        unfold nb078AlphaDummy095;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0084) 0))))
                    (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy097 f) from (by
                        unfold nb078AlphaDummy097;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0086 f) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy101) from (by
                          unfold nb078AlphaDummy101;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0088) 0))))
                      (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy102 f) from (by
                          unfold nb078AlphaDummy102;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0089 f) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy099) from (by
                            unfold nb078AlphaDummy099;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0085) 0))))
                        (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy100 f) from (by
                            unfold nb078AlphaDummy100;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0087 f) 0))))
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy000))).fv)
                            (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy089))).fv ∪
                      ((Class.cv (nb078AlphaDummy090))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078AlphaDummy091 f))).fv ∪
                      ((Class.cv (nb078AlphaDummy092 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy096) ≠ (nb078AlphaDummy103) from (by
                              unfold nb078AlphaDummy103;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0090) 0))))
                          (show (nb078AlphaDummy098 f) ≠ (nb078AlphaDummy105 f) from (by
                              unfold nb078AlphaDummy105;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0091 f) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy096) ≠ (nb078AlphaDummy104) from (by
                                unfold nb078AlphaDummy104;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0090) 1))))
                            (show (nb078AlphaDummy098 f) ≠ (nb078AlphaDummy106 f) from (by
                                unfold nb078AlphaDummy106;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0091 f) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy096))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy098 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy103) ≠ (nb078AlphaDummy110) from (by
          unfold nb078AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0094) 1)))) (show (nb078AlphaDummy105 f) ≠
        (nb078AlphaDummy113 f) from (by
          unfold nb078AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0095 f) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy103) ≠ (nb078AlphaDummy109) from (by
          unfold nb078AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0094) 0)))) (show (nb078AlphaDummy105 f) ≠
        (nb078AlphaDummy112 f) from (by
          unfold nb078AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0095 f) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy103) ≠ (nb078AlphaDummy107) from (by
          unfold nb078AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0092) 0)))) (show (nb078AlphaDummy105 f) ≠
        (nb078AlphaDummy108 f) from (by
          unfold nb078AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0093 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy111), (nb078AlphaDummy114 f)), ((nb078AlphaDummy110),
        (nb078AlphaDummy113 f)), ((nb078AlphaDummy109), (nb078AlphaDummy112 f)),
        ((nb078AlphaDummy107), (nb078AlphaDummy108 f)), ((nb078AlphaDummy103),
        (nb078AlphaDummy105 f)), ((nb078AlphaDummy104), (nb078AlphaDummy106 f)),
        ((nb078AlphaDummy096), (nb078AlphaDummy098 f)), ((nb078AlphaDummy095),
        (nb078AlphaDummy097 f)), ((nb078AlphaDummy101), (nb078AlphaDummy102 f)),
        ((nb078AlphaDummy099), (nb078AlphaDummy100 f)), ((nb078AlphaDummy090),
        (nb078AlphaDummy092 f)), ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
        ((nb078AlphaDummy093), (nb078AlphaDummy094 f)), ((nb078AlphaDummy011),
        (nb078AlphaDummy014 f)), ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
        ((nb078AlphaDummy009), (nb078AlphaDummy012 f)), ((nb078AlphaDummy015),
        (nb078AlphaDummy016 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy117) from (by
          unfold
            nb078AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0098)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy118 f) from (by
          unfold
            nb078AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy115)
        from (by
          unfold
            nb078AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0096)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy116 f) from (by
          unfold
            nb078AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy117)
        from (by
          unfold
            nb078AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0102)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy118 f) from (by
          unfold
            nb078AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy115)
        from (by
          unfold
            nb078AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0100)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy116 f) from (by
          unfold
            nb078AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy117) from (by
          unfold
            nb078AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0098)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy118 f) from (by
          unfold
            nb078AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy115)
        from (by
          unfold
            nb078AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0096)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy116 f) from (by
          unfold
            nb078AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy117)
        from (by
          unfold
            nb078AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0102)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy118 f) from (by
          unfold
            nb078AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy115)
        from (by
          unfold
            nb078AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0100)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy116 f) from (by
          unfold
            nb078AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy111), (nb078AlphaDummy114 f)), ((nb078AlphaDummy110),
        (nb078AlphaDummy113 f)), ((nb078AlphaDummy109), (nb078AlphaDummy112 f)),
        ((nb078AlphaDummy107), (nb078AlphaDummy108 f)), ((nb078AlphaDummy103),
        (nb078AlphaDummy105 f)), ((nb078AlphaDummy104), (nb078AlphaDummy106 f)),
        ((nb078AlphaDummy096), (nb078AlphaDummy098 f)), ((nb078AlphaDummy095),
        (nb078AlphaDummy097 f)), ((nb078AlphaDummy101), (nb078AlphaDummy102 f)),
        ((nb078AlphaDummy099), (nb078AlphaDummy100 f)), ((nb078AlphaDummy090),
        (nb078AlphaDummy092 f)), ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
        ((nb078AlphaDummy093), (nb078AlphaDummy094 f)), ((nb078AlphaDummy011),
        (nb078AlphaDummy014 f)), ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
        ((nb078AlphaDummy009), (nb078AlphaDummy012 f)), ((nb078AlphaDummy015),
        (nb078AlphaDummy016 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy103))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy105
        f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy121) from (by
          unfold
            nb078AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0106)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy122 f) from (by
          unfold
            nb078AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy119)
        from (by
          unfold
            nb078AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0104)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy120 f) from (by
          unfold
            nb078AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy121)
        from (by
          unfold
            nb078AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0106)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy122 f) from (by
          unfold
            nb078AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy119)
        from (by
          unfold
            nb078AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0104)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy120 f) from (by
          unfold
            nb078AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy123) from (by
          unfold
            nb078AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0110)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy124 f) from (by
          unfold
            nb078AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy119)
        from (by
          unfold
            nb078AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0108)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy120 f) from (by
          unfold
            nb078AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy111) ≠
        (nb078AlphaDummy123) from (by
          unfold
            nb078AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0110)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy124 f) from (by
          unfold
            nb078AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy119)
        from (by
          unfold
            nb078AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0108)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy120 f) from (by
          unfold
            nb078AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy103) ≠ (nb078AlphaDummy107) from (by
                                        unfold nb078AlphaDummy107;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0092)
                                                0)))) (show (nb078AlphaDummy105 f) ≠
                                        (nb078AlphaDummy108 f) from (by
                                        unfold nb078AlphaDummy108;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0093 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy107), (nb078AlphaDummy108 f)),
                                    ((nb078AlphaDummy103), (nb078AlphaDummy105 f)),
                                    ((nb078AlphaDummy104), (nb078AlphaDummy106 f)),
                                    ((nb078AlphaDummy096), (nb078AlphaDummy098 f)),
                                    ((nb078AlphaDummy095), (nb078AlphaDummy097 f)),
                                    ((nb078AlphaDummy101), (nb078AlphaDummy102 f)),
                                    ((nb078AlphaDummy099), (nb078AlphaDummy100 f)),
                                    ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
                                    ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
                                    ((nb078AlphaDummy093), (nb078AlphaDummy094 f)),
                                    ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
                                    ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                                    ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                                    ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
                                    ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy103) ≠ (nb078AlphaDummy107) from
                                    (by
                                      unfold nb078AlphaDummy107;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0092)
                                              0)))) (show
                                    (nb078AlphaDummy105 f) ≠ (nb078AlphaDummy108 f) from
                                    (by
                                      unfold nb078AlphaDummy108;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0093 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy103) ≠ (nb078AlphaDummy107) from (by
                                        unfold nb078AlphaDummy107;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0092)
                                                0)))) (show (nb078AlphaDummy105 f) ≠
                                        (nb078AlphaDummy108 f) from (by
                                        unfold nb078AlphaDummy108;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0093 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy107), (nb078AlphaDummy108 f)),
                                    ((nb078AlphaDummy103), (nb078AlphaDummy105 f)),
                                    ((nb078AlphaDummy104), (nb078AlphaDummy106 f)),
                                    ((nb078AlphaDummy096), (nb078AlphaDummy098 f)),
                                    ((nb078AlphaDummy095), (nb078AlphaDummy097 f)),
                                    ((nb078AlphaDummy101), (nb078AlphaDummy102 f)),
                                    ((nb078AlphaDummy099), (nb078AlphaDummy100 f)),
                                    ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
                                    ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
                                    ((nb078AlphaDummy093), (nb078AlphaDummy094 f)),
                                    ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
                                    ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                                    ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                                    ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
                                    ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy096) from
                      (by
                        unfold nb078AlphaDummy096;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0084) 1))))
                    (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy098 f) from (by
                        unfold nb078AlphaDummy098;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0086 f) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy095) from (by
                          unfold nb078AlphaDummy095;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0084) 0))))
                      (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy097 f) from (by
                          unfold nb078AlphaDummy097;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0086 f) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy101) from (by
                            unfold nb078AlphaDummy101;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0088) 0))))
                        (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy102 f) from (by
                            unfold nb078AlphaDummy102;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0089 f) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy099) from (by
                              unfold nb078AlphaDummy099;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0085) 0))))
                          (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy100 f) from (by
                              unfold nb078AlphaDummy100;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0087 f) 0))))
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy000))).fv)
                              (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078AlphaDummy089))).fv ∪
                        ((Class.cv (nb078AlphaDummy090))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy091 f))).fv ∪
                        ((Class.cv (nb078AlphaDummy092 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy096) ≠ (nb078AlphaDummy103) from (by
                                unfold nb078AlphaDummy103;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0090) 0))))
                            (show (nb078AlphaDummy098 f) ≠ (nb078AlphaDummy105 f) from (by
                                unfold nb078AlphaDummy105;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0091 f) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy096) ≠ (nb078AlphaDummy104) from (by
                                  unfold nb078AlphaDummy104;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0090) 1))))
                              (show (nb078AlphaDummy098 f) ≠ (nb078AlphaDummy106 f) from
                                (by
                                  unfold nb078AlphaDummy106;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0091 f) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy096))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy098 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy103) ≠ (nb078AlphaDummy110) from (by
          unfold nb078AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0094) 1)))) (show (nb078AlphaDummy105 f) ≠
        (nb078AlphaDummy113 f) from (by
          unfold nb078AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0095 f) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy103) ≠ (nb078AlphaDummy109) from (by
          unfold nb078AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0094) 0)))) (show (nb078AlphaDummy105 f) ≠
        (nb078AlphaDummy112 f) from (by
          unfold nb078AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0095 f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy103) ≠ (nb078AlphaDummy107)
        from (by
          unfold nb078AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0092)
                  0)))) (show (nb078AlphaDummy105 f) ≠ (nb078AlphaDummy108 f) from (by
          unfold nb078AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0093 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy111), (nb078AlphaDummy114 f)), ((nb078AlphaDummy110),
        (nb078AlphaDummy113 f)), ((nb078AlphaDummy109), (nb078AlphaDummy112 f)),
        ((nb078AlphaDummy107), (nb078AlphaDummy108 f)), ((nb078AlphaDummy103),
        (nb078AlphaDummy105 f)), ((nb078AlphaDummy104), (nb078AlphaDummy106 f)),
        ((nb078AlphaDummy096), (nb078AlphaDummy098 f)), ((nb078AlphaDummy095),
        (nb078AlphaDummy097 f)), ((nb078AlphaDummy101), (nb078AlphaDummy102 f)),
        ((nb078AlphaDummy099), (nb078AlphaDummy100 f)), ((nb078AlphaDummy090),
        (nb078AlphaDummy092 f)), ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
        ((nb078AlphaDummy093), (nb078AlphaDummy094 f)), ((nb078AlphaDummy011),
        (nb078AlphaDummy014 f)), ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
        ((nb078AlphaDummy009), (nb078AlphaDummy012 f)), ((nb078AlphaDummy015),
        (nb078AlphaDummy016 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy117) from (by
          unfold
            nb078AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0098)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy118 f) from (by
          unfold
            nb078AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy115)
        from (by
          unfold
            nb078AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0096)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy116 f) from (by
          unfold
            nb078AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy117)
        from (by
          unfold
            nb078AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0102)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy118 f) from (by
          unfold
            nb078AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy115)
        from (by
          unfold
            nb078AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0100)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy116 f) from (by
          unfold
            nb078AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy117) from (by
          unfold
            nb078AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0098)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy118 f) from (by
          unfold
            nb078AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy115)
        from (by
          unfold
            nb078AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0096)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy116 f) from (by
          unfold
            nb078AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy117)
        from (by
          unfold
            nb078AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0102)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy118 f) from (by
          unfold
            nb078AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy115)
        from (by
          unfold
            nb078AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0100)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy116 f) from (by
          unfold
            nb078AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy111), (nb078AlphaDummy114 f)), ((nb078AlphaDummy110),
        (nb078AlphaDummy113 f)), ((nb078AlphaDummy109), (nb078AlphaDummy112 f)),
        ((nb078AlphaDummy107), (nb078AlphaDummy108 f)), ((nb078AlphaDummy103),
        (nb078AlphaDummy105 f)), ((nb078AlphaDummy104), (nb078AlphaDummy106 f)),
        ((nb078AlphaDummy096), (nb078AlphaDummy098 f)), ((nb078AlphaDummy095),
        (nb078AlphaDummy097 f)), ((nb078AlphaDummy101), (nb078AlphaDummy102 f)),
        ((nb078AlphaDummy099), (nb078AlphaDummy100 f)), ((nb078AlphaDummy090),
        (nb078AlphaDummy092 f)), ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
        ((nb078AlphaDummy093), (nb078AlphaDummy094 f)), ((nb078AlphaDummy011),
        (nb078AlphaDummy014 f)), ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
        ((nb078AlphaDummy009), (nb078AlphaDummy012 f)), ((nb078AlphaDummy015),
        (nb078AlphaDummy016 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy103))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy105
        f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy121) from (by
          unfold
            nb078AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0106)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy122 f) from (by
          unfold
            nb078AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy119)
        from (by
          unfold
            nb078AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0104)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy120 f) from (by
          unfold
            nb078AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy121)
        from (by
          unfold
            nb078AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0106)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy122 f) from (by
          unfold
            nb078AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy119)
        from (by
          unfold
            nb078AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0104)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy120 f) from (by
          unfold
            nb078AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy123) from (by
          unfold
            nb078AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0110)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy124 f) from (by
          unfold
            nb078AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy119)
        from (by
          unfold
            nb078AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0108)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy120 f) from (by
          unfold
            nb078AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy111) ≠
        (nb078AlphaDummy123) from (by
          unfold
            nb078AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0110)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy124 f) from (by
          unfold
            nb078AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy119)
        from (by
          unfold
            nb078AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0108)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy120 f) from (by
          unfold
            nb078AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy103) ≠ (nb078AlphaDummy107) from
                                        (by
                                          unfold nb078AlphaDummy107;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0092)
                                                  0)))) (show (nb078AlphaDummy105 f) ≠
        (nb078AlphaDummy108 f) from (by
                                          unfold nb078AlphaDummy108;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0093 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy107), (nb078AlphaDummy108 f)),
                                      ((nb078AlphaDummy103), (nb078AlphaDummy105 f)),
                                      ((nb078AlphaDummy104), (nb078AlphaDummy106 f)),
                                      ((nb078AlphaDummy096), (nb078AlphaDummy098 f)),
                                      ((nb078AlphaDummy095), (nb078AlphaDummy097 f)),
                                      ((nb078AlphaDummy101), (nb078AlphaDummy102 f)),
                                      ((nb078AlphaDummy099), (nb078AlphaDummy100 f)),
                                      ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
                                      ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
                                      ((nb078AlphaDummy093), (nb078AlphaDummy094 f)),
                                      ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
                                      ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                                      ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                                      ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
                                      ((nb078AlphaDummy000), f),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy103) ≠ (nb078AlphaDummy107) from (by
                                        unfold nb078AlphaDummy107;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0092)
                                                0)))) (show (nb078AlphaDummy105 f) ≠
                                        (nb078AlphaDummy108 f) from (by
                                        unfold nb078AlphaDummy108;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0093 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy103) ≠ (nb078AlphaDummy107) from
                                        (by
                                          unfold nb078AlphaDummy107;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0092)
                                                  0)))) (show (nb078AlphaDummy105 f) ≠
        (nb078AlphaDummy108 f) from (by
                                          unfold nb078AlphaDummy108;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0093 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy107), (nb078AlphaDummy108 f)),
                                      ((nb078AlphaDummy103), (nb078AlphaDummy105 f)),
                                      ((nb078AlphaDummy104), (nb078AlphaDummy106 f)),
                                      ((nb078AlphaDummy096), (nb078AlphaDummy098 f)),
                                      ((nb078AlphaDummy095), (nb078AlphaDummy097 f)),
                                      ((nb078AlphaDummy101), (nb078AlphaDummy102 f)),
                                      ((nb078AlphaDummy099), (nb078AlphaDummy100 f)),
                                      ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
                                      ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
                                      ((nb078AlphaDummy093), (nb078AlphaDummy094 f)),
                                      ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
                                      ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                                      ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                                      ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
                                      ((nb078AlphaDummy000), f),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part047`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0016`. -/
@[expose]
noncomputable def nb078SplitAlpha0016 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb078AlphaDummy129), (nb078AlphaDummy130 f)),
        ((nb078AlphaDummy127), (nb078AlphaDummy128 f)),
        ((nb078AlphaDummy096), (nb078AlphaDummy098 f)),
        ((nb078AlphaDummy095), (nb078AlphaDummy097 f)),
        ((nb078AlphaDummy125), (nb078AlphaDummy126 f)),
        ((nb078AlphaDummy099), (nb078AlphaDummy100 f)),
        ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
        ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
        ((nb078AlphaDummy093), (nb078AlphaDummy094 f)),
        ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
        ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
        ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
        ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy129))
          (synCphi (Class.cv (nb078AlphaDummy096)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy129))
            (synCphi (Class.cv (nb078AlphaDummy096))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy130 f))
          (synCphi (Class.cv (nb078AlphaDummy098 f)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy130 f))
            (synCphi (Class.cv (nb078AlphaDummy098 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy096) ≠ (nb078AlphaDummy103) from
                    (by
                      unfold nb078AlphaDummy103;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0090) 0))))
                  (show (nb078AlphaDummy098 f) ≠ (nb078AlphaDummy105 f) from (by
                      unfold nb078AlphaDummy105;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0091 f) 0))))
                  (TAlphaVar.there (show (nb078AlphaDummy096) ≠ (nb078AlphaDummy104) from
                      (by
                        unfold nb078AlphaDummy104;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0090) 1))))
                    (show (nb078AlphaDummy098 f) ≠ (nb078AlphaDummy106 f) from (by
                        unfold nb078AlphaDummy106;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0091 f) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy096) ≠ (nb078AlphaDummy129) from (by
                          unfold nb078AlphaDummy129;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0120) 0))))
                      (show (nb078AlphaDummy098 f) ≠ (nb078AlphaDummy130 f) from (by
                          unfold nb078AlphaDummy130;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0121 f) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy096) ≠ (nb078AlphaDummy127) from (by
                            unfold nb078AlphaDummy127;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0118) 0))))
                        (show (nb078AlphaDummy098 f) ≠ (nb078AlphaDummy128 f) from (by
                            unfold nb078AlphaDummy128;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0119 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy096))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy098 f))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy103) ≠ (nb078AlphaDummy110) from (by
                                        unfold nb078AlphaDummy110;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0094)
                                                1)))) (show (nb078AlphaDummy105 f) ≠
                                        (nb078AlphaDummy113 f) from (by
                                        unfold nb078AlphaDummy113;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0095 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy103) ≠ (nb078AlphaDummy109) from
                                        (by
                                          unfold nb078AlphaDummy109;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0094)
                                                  0)))) (show (nb078AlphaDummy105 f) ≠
        (nb078AlphaDummy112 f) from (by
                                          unfold nb078AlphaDummy112;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0095 f) 0))))
                                      (TAlphaVar.there (show (nb078AlphaDummy103) ≠
        (nb078AlphaDummy107) from (by
          unfold nb078AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0092) 0)))) (show (nb078AlphaDummy105 f) ≠
        (nb078AlphaDummy108 f) from (by
          unfold nb078AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0093 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb078AlphaDummy111),
        (nb078AlphaDummy114 f)), ((nb078AlphaDummy110), (nb078AlphaDummy113 f)),
                                        ((nb078AlphaDummy109), (nb078AlphaDummy112 f)),
                                        ((nb078AlphaDummy107), (nb078AlphaDummy108 f)),
                                        ((nb078AlphaDummy103), (nb078AlphaDummy105 f)),
                                        ((nb078AlphaDummy104), (nb078AlphaDummy106 f)),
                                        ((nb078AlphaDummy129), (nb078AlphaDummy130 f)),
                                        ((nb078AlphaDummy127), (nb078AlphaDummy128 f)),
                                        ((nb078AlphaDummy096), (nb078AlphaDummy098 f)),
                                        ((nb078AlphaDummy095), (nb078AlphaDummy097 f)),
                                        ((nb078AlphaDummy125), (nb078AlphaDummy126 f)),
                                        ((nb078AlphaDummy099), (nb078AlphaDummy100 f)),
                                        ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
                                        ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
                                        ((nb078AlphaDummy093), (nb078AlphaDummy094 f)),
                                        ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
                                        ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                                        ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                                        ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
                                        ((nb078AlphaDummy000), f),
                                        ((nb078AlphaDummy004), y),
                                        ((nb078AlphaDummy003), x)]
                                      (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy110) ≠
        (nb078AlphaDummy117) from (by
          unfold
            nb078AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0098)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy118 f) from (by
          unfold
            nb078AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy115)
        from (by
          unfold
            nb078AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0096)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy116 f) from (by
          unfold
            nb078AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy117)
        from (by
          unfold
            nb078AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0102)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy118 f) from (by
          unfold
            nb078AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy115)
        from (by
          unfold
            nb078AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0100)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy116 f) from (by
          unfold
            nb078AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy117) from (by
          unfold
            nb078AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0098)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy118 f) from (by
          unfold
            nb078AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy115)
        from (by
          unfold
            nb078AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0096)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy116 f) from (by
          unfold
            nb078AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy117)
        from (by
          unfold
            nb078AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0102)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy118 f) from (by
          unfold
            nb078AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy115)
        from (by
          unfold
            nb078AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0100)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy116 f) from (by
          unfold
            nb078AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb078AlphaDummy111), (nb078AlphaDummy114 f)),
        ((nb078AlphaDummy110), (nb078AlphaDummy113 f)), ((nb078AlphaDummy109),
        (nb078AlphaDummy112 f)), ((nb078AlphaDummy107), (nb078AlphaDummy108 f)),
        ((nb078AlphaDummy103), (nb078AlphaDummy105 f)), ((nb078AlphaDummy104),
        (nb078AlphaDummy106 f)), ((nb078AlphaDummy129), (nb078AlphaDummy130 f)),
        ((nb078AlphaDummy127), (nb078AlphaDummy128 f)), ((nb078AlphaDummy096),
        (nb078AlphaDummy098 f)), ((nb078AlphaDummy095), (nb078AlphaDummy097 f)),
        ((nb078AlphaDummy125), (nb078AlphaDummy126 f)), ((nb078AlphaDummy099),
        (nb078AlphaDummy100 f)), ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
        ((nb078AlphaDummy089), (nb078AlphaDummy091 f)), ((nb078AlphaDummy093),
        (nb078AlphaDummy094 f)), ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
        ((nb078AlphaDummy010), (nb078AlphaDummy013 f)), ((nb078AlphaDummy009),
        (nb078AlphaDummy012 f)), ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy110) ≠
        (nb078AlphaDummy121) from (by
          unfold
            nb078AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0106)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy122 f) from (by
          unfold
            nb078AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy119)
        from (by
          unfold
            nb078AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0104)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy120 f) from (by
          unfold
            nb078AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy121)
        from (by
          unfold
            nb078AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0106)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy122 f) from (by
          unfold
            nb078AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy119)
        from (by
          unfold
            nb078AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0104)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy120 f) from (by
          unfold
            nb078AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy123) from (by
          unfold
            nb078AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0110)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy124 f) from (by
          unfold
            nb078AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy119)
        from (by
          unfold
            nb078AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0108)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy120 f) from (by
          unfold
            nb078AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy111) ≠
        (nb078AlphaDummy123) from (by
          unfold
            nb078AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0110)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy124 f) from (by
          unfold
            nb078AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy119)
        from (by
          unfold
            nb078AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0108)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy120 f) from (by
          unfold
            nb078AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy103) ≠ (nb078AlphaDummy107) from (by
                                unfold nb078AlphaDummy107;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0092) 0))))
                            (show (nb078AlphaDummy105 f) ≠ (nb078AlphaDummy108 f) from (by
                                unfold nb078AlphaDummy108;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0093 f) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb078AlphaDummy107), (nb078AlphaDummy108 f)),
                            ((nb078AlphaDummy103), (nb078AlphaDummy105 f)),
                            ((nb078AlphaDummy104), (nb078AlphaDummy106 f)),
                            ((nb078AlphaDummy129), (nb078AlphaDummy130 f)),
                            ((nb078AlphaDummy127), (nb078AlphaDummy128 f)),
                            ((nb078AlphaDummy096), (nb078AlphaDummy098 f)),
                            ((nb078AlphaDummy095), (nb078AlphaDummy097 f)),
                            ((nb078AlphaDummy125), (nb078AlphaDummy126 f)),
                            ((nb078AlphaDummy099), (nb078AlphaDummy100 f)),
                            ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
                            ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
                            ((nb078AlphaDummy093), (nb078AlphaDummy094 f)),
                            ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
                            ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                            ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                            ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
                            ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
                            ((nb078AlphaDummy003), x)]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy103) ≠ (nb078AlphaDummy107) from (by
                              unfold nb078AlphaDummy107;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0092) 0))))
                          (show (nb078AlphaDummy105 f) ≠ (nb078AlphaDummy108 f) from (by
                              unfold nb078AlphaDummy108;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0093 f) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy103) ≠ (nb078AlphaDummy107) from (by
                                unfold nb078AlphaDummy107;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0092) 0))))
                            (show (nb078AlphaDummy105 f) ≠ (nb078AlphaDummy108 f) from (by
                                unfold nb078AlphaDummy108;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0093 f) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb078AlphaDummy107), (nb078AlphaDummy108 f)),
                            ((nb078AlphaDummy103), (nb078AlphaDummy105 f)),
                            ((nb078AlphaDummy104), (nb078AlphaDummy106 f)),
                            ((nb078AlphaDummy129), (nb078AlphaDummy130 f)),
                            ((nb078AlphaDummy127), (nb078AlphaDummy128 f)),
                            ((nb078AlphaDummy096), (nb078AlphaDummy098 f)),
                            ((nb078AlphaDummy095), (nb078AlphaDummy097 f)),
                            ((nb078AlphaDummy125), (nb078AlphaDummy126 f)),
                            ((nb078AlphaDummy099), (nb078AlphaDummy100 f)),
                            ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
                            ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
                            ((nb078AlphaDummy093), (nb078AlphaDummy094 f)),
                            ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
                            ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                            ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                            ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
                            ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
                            ((nb078AlphaDummy003), x)]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb078AlphaDummy096) ≠ (nb078AlphaDummy103) from (by
                        unfold nb078AlphaDummy103;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0090) 0))))
                    (show (nb078AlphaDummy098 f) ≠ (nb078AlphaDummy105 f) from (by
                        unfold nb078AlphaDummy105;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0091 f) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy096) ≠ (nb078AlphaDummy104) from (by
                          unfold nb078AlphaDummy104;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0090) 1))))
                      (show (nb078AlphaDummy098 f) ≠ (nb078AlphaDummy106 f) from (by
                          unfold nb078AlphaDummy106;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0091 f) 1))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy096) ≠ (nb078AlphaDummy129) from (by
                            unfold nb078AlphaDummy129;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0120) 0))))
                        (show (nb078AlphaDummy098 f) ≠ (nb078AlphaDummy130 f) from (by
                            unfold nb078AlphaDummy130;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0121 f) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy096) ≠ (nb078AlphaDummy127) from (by
                              unfold nb078AlphaDummy127;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0118) 0))))
                          (show (nb078AlphaDummy098 f) ≠ (nb078AlphaDummy128 f) from (by
                              unfold nb078AlphaDummy128;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0119 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy096))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy098 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb078AlphaDummy103) ≠ (nb078AlphaDummy110) from
                                        (by
                                          unfold nb078AlphaDummy110;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0094)
                                                  1)))) (show (nb078AlphaDummy105 f) ≠
        (nb078AlphaDummy113 f) from (by
                                          unfold nb078AlphaDummy113;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0095 f) 1))))
                                      (TAlphaVar.there (show (nb078AlphaDummy103) ≠
        (nb078AlphaDummy109) from (by
          unfold nb078AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0094) 0)))) (show (nb078AlphaDummy105 f) ≠
        (nb078AlphaDummy112 f) from (by
          unfold nb078AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0095 f) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy103) ≠ (nb078AlphaDummy107) from (by
          unfold nb078AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0092) 0)))) (show (nb078AlphaDummy105 f) ≠
        (nb078AlphaDummy108 f) from (by
          unfold nb078AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0093 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb078AlphaDummy111),
        (nb078AlphaDummy114 f)), ((nb078AlphaDummy110), (nb078AlphaDummy113 f)),
        ((nb078AlphaDummy109), (nb078AlphaDummy112 f)), ((nb078AlphaDummy107),
        (nb078AlphaDummy108 f)), ((nb078AlphaDummy103), (nb078AlphaDummy105 f)),
        ((nb078AlphaDummy104), (nb078AlphaDummy106 f)), ((nb078AlphaDummy129),
        (nb078AlphaDummy130 f)), ((nb078AlphaDummy127), (nb078AlphaDummy128 f)),
        ((nb078AlphaDummy096), (nb078AlphaDummy098 f)), ((nb078AlphaDummy095),
        (nb078AlphaDummy097 f)), ((nb078AlphaDummy125), (nb078AlphaDummy126 f)),
        ((nb078AlphaDummy099), (nb078AlphaDummy100 f)), ((nb078AlphaDummy090),
        (nb078AlphaDummy092 f)), ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
        ((nb078AlphaDummy093), (nb078AlphaDummy094 f)), ((nb078AlphaDummy011),
        (nb078AlphaDummy014 f)), ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
        ((nb078AlphaDummy009), (nb078AlphaDummy012 f)), ((nb078AlphaDummy015),
        (nb078AlphaDummy016 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy110) ≠
        (nb078AlphaDummy117) from (by
          unfold
            nb078AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0098)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy118 f) from (by
          unfold
            nb078AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy115)
        from (by
          unfold
            nb078AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0096)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy116 f) from (by
          unfold
            nb078AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy117)
        from (by
          unfold
            nb078AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0102)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy118 f) from (by
          unfold
            nb078AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy115)
        from (by
          unfold
            nb078AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0100)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy116 f) from (by
          unfold
            nb078AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy117) from (by
          unfold
            nb078AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0098)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy118 f) from (by
          unfold
            nb078AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy115)
        from (by
          unfold
            nb078AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0096)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy116 f) from (by
          unfold
            nb078AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy117)
        from (by
          unfold
            nb078AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0102)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy118 f) from (by
          unfold
            nb078AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy115)
        from (by
          unfold
            nb078AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0100)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy116 f) from (by
          unfold
            nb078AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy111), (nb078AlphaDummy114 f)), ((nb078AlphaDummy110),
        (nb078AlphaDummy113 f)), ((nb078AlphaDummy109), (nb078AlphaDummy112 f)),
        ((nb078AlphaDummy107), (nb078AlphaDummy108 f)), ((nb078AlphaDummy103),
        (nb078AlphaDummy105 f)), ((nb078AlphaDummy104), (nb078AlphaDummy106 f)),
        ((nb078AlphaDummy129), (nb078AlphaDummy130 f)), ((nb078AlphaDummy127),
        (nb078AlphaDummy128 f)), ((nb078AlphaDummy096), (nb078AlphaDummy098 f)),
        ((nb078AlphaDummy095), (nb078AlphaDummy097 f)), ((nb078AlphaDummy125),
        (nb078AlphaDummy126 f)), ((nb078AlphaDummy099), (nb078AlphaDummy100 f)),
        ((nb078AlphaDummy090), (nb078AlphaDummy092 f)), ((nb078AlphaDummy089),
        (nb078AlphaDummy091 f)), ((nb078AlphaDummy093), (nb078AlphaDummy094 f)),
        ((nb078AlphaDummy011), (nb078AlphaDummy014 f)), ((nb078AlphaDummy010),
        (nb078AlphaDummy013 f)), ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
        ((nb078AlphaDummy015), (nb078AlphaDummy016 f)), ((nb078AlphaDummy000), f),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy103))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy103))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy110) ≠
        (nb078AlphaDummy121) from (by
          unfold
            nb078AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0106)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy122 f) from (by
          unfold
            nb078AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy119)
        from (by
          unfold
            nb078AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0104)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy120 f) from (by
          unfold
            nb078AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy121)
        from (by
          unfold
            nb078AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0106)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy122 f) from (by
          unfold
            nb078AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy119)
        from (by
          unfold
            nb078AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0104)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy120 f) from (by
          unfold
            nb078AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy123) from (by
          unfold
            nb078AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0110)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy124 f) from (by
          unfold
            nb078AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy119)
        from (by
          unfold
            nb078AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0108)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy120 f) from (by
          unfold
            nb078AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy111) ≠
        (nb078AlphaDummy123) from (by
          unfold
            nb078AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0110)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy124 f) from (by
          unfold
            nb078AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy119)
        from (by
          unfold
            nb078AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0108)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy120 f) from (by
          unfold
            nb078AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078AlphaDummy103) ≠ (nb078AlphaDummy107) from (by
                                  unfold nb078AlphaDummy107;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0092) 0))))
                              (show (nb078AlphaDummy105 f) ≠ (nb078AlphaDummy108 f) from
                                (by
                                  unfold nb078AlphaDummy108;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0093 f) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb078AlphaDummy107), (nb078AlphaDummy108 f)),
                              ((nb078AlphaDummy103), (nb078AlphaDummy105 f)),
                              ((nb078AlphaDummy104), (nb078AlphaDummy106 f)),
                              ((nb078AlphaDummy129), (nb078AlphaDummy130 f)),
                              ((nb078AlphaDummy127), (nb078AlphaDummy128 f)),
                              ((nb078AlphaDummy096), (nb078AlphaDummy098 f)),
                              ((nb078AlphaDummy095), (nb078AlphaDummy097 f)),
                              ((nb078AlphaDummy125), (nb078AlphaDummy126 f)),
                              ((nb078AlphaDummy099), (nb078AlphaDummy100 f)),
                              ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
                              ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
                              ((nb078AlphaDummy093), (nb078AlphaDummy094 f)),
                              ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
                              ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                              ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                              ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
                              ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
                              ((nb078AlphaDummy003), x)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy103) ≠ (nb078AlphaDummy107) from (by
                                unfold nb078AlphaDummy107;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0092) 0))))
                            (show (nb078AlphaDummy105 f) ≠ (nb078AlphaDummy108 f) from (by
                                unfold nb078AlphaDummy108;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0093 f) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078AlphaDummy103) ≠ (nb078AlphaDummy107) from (by
                                  unfold nb078AlphaDummy107;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0092) 0))))
                              (show (nb078AlphaDummy105 f) ≠ (nb078AlphaDummy108 f) from
                                (by
                                  unfold nb078AlphaDummy108;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0093 f) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb078AlphaDummy107), (nb078AlphaDummy108 f)),
                              ((nb078AlphaDummy103), (nb078AlphaDummy105 f)),
                              ((nb078AlphaDummy104), (nb078AlphaDummy106 f)),
                              ((nb078AlphaDummy129), (nb078AlphaDummy130 f)),
                              ((nb078AlphaDummy127), (nb078AlphaDummy128 f)),
                              ((nb078AlphaDummy096), (nb078AlphaDummy098 f)),
                              ((nb078AlphaDummy095), (nb078AlphaDummy097 f)),
                              ((nb078AlphaDummy125), (nb078AlphaDummy126 f)),
                              ((nb078AlphaDummy099), (nb078AlphaDummy100 f)),
                              ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
                              ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
                              ((nb078AlphaDummy093), (nb078AlphaDummy094 f)),
                              ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
                              ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                              ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                              ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
                              ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
                              ((nb078AlphaDummy003), x)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
